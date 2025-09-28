try:
    from lark import Lark, exceptions
    import os
    from .nar_parsers import (VarParser, ActionParser, ReturnParser, Variable, Number, expand,
                                            Conversion, Condition, Comparison, traverse, ID, 
                                            FuncCall, Expr, Bool, Action, Return, flatten_condition)
    from .pyramid_exceptions import *
    from typing import Union
except ImportError:
    raise ImportError("You seem to have missed some dependencies. Make sure to check the requirements.")


def ConditionProcessor(variable: Variable, traversed_condition: list):
    """
    The ConditionProcessor() traverses a condition to inject the new Variable structure in every occurrence of the old
    one. This is part of the Knowledge-Sharing Mechanism.
    :param variable: The new Variable structure.
    :param traversed_condition: Items of a condition (Flattened).
    :return: Nothing, it only injects the new Variable structure.
    """
    if not isinstance(traversed_condition, list):
        traversed_condition = [traversed_condition]

    for i, condition in enumerate(traversed_condition):
        traversed_condition[i] = condition_processor_util(variable, condition)

    return traversed_condition


def condition_processor_util(variable: Variable, condition):
    """
    The condition_processor_util() is a utility function that helps in condition processing.
    :param variable: The new Variable structure.
    :param condition: The condition (Flattened or Condition structure).
    :return: Nothing, it only injects the new Variable structure.
    """
    if isinstance(condition, Condition):
        condition.condition = condition_processor_util(variable, condition.condition)
    elif isinstance(condition, list):
        for i, c in enumerate(condition):
            condition[i] = ConditionProcessor(variable, c)
    elif isinstance(condition, Comparison):
        condition.inject_variable(variable)

    return condition


class KnowledgeSharingChannel:
    """
    This is a base channel class which must be defined to handle the processing of the Knowledge-Sharing Mechanism.
    """
    def build(self):
        raise NotImplementedError

    def overflow_check(self, component):
        raise NotImplementedError

    def convert(self):
        raise NotImplementedError


class VAC(KnowledgeSharingChannel):
    """
    This is a channel class handles the knowledge sharing between the Var and Action components.
    """
    def __init__(self, variables: list, actions: list):
        self.__variables = variables
        self.__actions = actions
        self.__map = []
        self.__conversions = []

    def build(self):
        """
        The build() method builds all the VAC contracts.
        :return:
        """
        removed_actions = []

        for idx, action in enumerate(self.__actions):
            
            if self.__actions[idx].lvalue.freeze_state_at is None:
                self.__actions[idx].lvalue.freeze(idx)

            if self.__actions[idx].rvalue.freeze_state_at is None:
                self.__actions[idx].rvalue.freeze(idx)
                    
            for n, next_action in enumerate(self.__actions[idx+1:]):

                if action.lvalue in next_action.expansion:
                    if (isinstance(next_action.rvalue, Expr) and not isinstance(next_action.rvalue, Bool)):
                        self.__actions[idx+n+1].rvalue = self.__actions[idx+n+1].rvalue.variable_update(self.__actions[idx+n+1].lvalue)
                
                if self.__actions[idx+n+1].lvalue.freeze_state_at is None:
                    self.__actions[idx+n+1].lvalue.freeze(idx+n+1)

                if self.__actions[idx+n+1].rvalue.freeze_state_at is None:
                    self.__actions[idx+n+1].rvalue.freeze(idx+n+1)

                self.__actions[idx+n+1].expansion = expand(self.__actions[idx+n+1].rvalue)

            vars_temp = [variable for variable in action.expansion if isinstance(variable, (Variable, ID))]
            
            for idy, var in enumerate(self.__variables):
                self.__actions[idx].condition = ConditionProcessor(var.variable, traversed_condition=action.condition)
                map_ = {'variable': var, 'action': action,
                        'lvalue': False, 'rvalue': False, 'vars': vars_temp}

                if var.variable == action.lvalue:
                    self.__variables[idy].variable.write_permission = True
                    self.__actions[idx].lvalue.var_type = var.variable.var_type
                    self.__variables[idy].variable.freeze(idx)
                    map_['lvalue'] = True
               
                # Rvalues and Function Args
                k = 0
                for i, item in enumerate(self.__actions[idx].expansion):
                    
                    modified = False
                    
                    if isinstance(item, FuncCall):
            
                        self.__actions[idx].expansion[i] = self.__actions[idx].expansion[i].variable_update(self.__variables[idy].variable,
                                                                                                             share_old_flag=True)
                        args = []
                        for j, arg in enumerate(item.args):
                            if isinstance(arg, ID) and arg == var.variable:
                                args.append(self.__variables[idy].variable)
                            elif isinstance(arg, Expr):
                                item.args[j].freeze(idx)
                                args.append(arg)

                        item.args = args

                    elif isinstance(item, Expr):
                        self.__actions[idx].expansion[i].freeze_state_at = idx
                        self.__actions[idx].rvalue = self.__actions[idx].rvalue.variable_update(self.__actions[idx].expansion[i], 
                                                                                                share_old_flag=True, freeze_state=True)

                    if item == var.variable:
                        if isinstance(item, (Variable, ID)):
                            self.__actions[idx].expansion[i] = var.variable
                            self.__actions[idx].expansion[i].freeze(idx)
                        
                        self.__actions[idx].rvalue = self.__actions[idx].rvalue.variable_update(
                            self.__actions[idx].expansion[i],
                            freeze_state=True
                        )
                        
                        vars_temp[k] = self.__variables[idy].variable
                        k += 1
                        map_['rvalue'] = True
                        
                        for a in self.__actions[idx:]:
                            if item == a.lvalue:
                                modified = True
                        
                        if modified:
                            self.__actions[idx].expansion[i].old_predicate_flag = True
                            self.__actions[idx].rvalue = self.__actions[idx].rvalue.variable_update(self.__actions[idx].expansion[i], 
                                                                                                    share_old_flag=True)
                self.__actions[idx].expansion = expand(self.__actions[idx].rvalue)
                self.__map.append(map_)


        # Lookahead Write Permissions and Action Reduction
        for idx, action in enumerate(self.__actions):
            target_action_indices = [idx+t+1 for t, na in enumerate(self.__actions[idx+1:]) if na.lvalue == action.lvalue]
            target_action_indices.insert(0, idx)
            target = 0
            lvalue_condition_dependent = False

            for next_action in self.__actions[idx:]:
                if isinstance(next_action.condition[0], Condition) and not lvalue_condition_dependent:
                    lvalue_condition_dependent = next_action.condition[0].does_variable_exist(action.lvalue)

            for n, next_action in enumerate(self.__actions[idx+1:]):

                for v, item in enumerate(next_action.expansion):
                    if isinstance(item, (Variable, ID)) and item == action.lvalue:
                        self.__actions[idx+n+1].expansion[v].write_permission = True
                
                occurences = next_action.rvalue.find(action.lvalue, [])

                for occurence in occurences:
                    
                    if (occurence.freeze_state_at > action.rvalue.freeze_state_at 
                        and not lvalue_condition_dependent and self.__actions[idx].condition == ['ANY']
                       ):
                        if isinstance(self.__actions[target_action_indices[target]].rvalue, Expr):
                  
                            for element in self.__actions[target_action_indices[target]].expansion:

                                if isinstance(element, Expr):

                                    element.freeze(self.__actions[target_action_indices[target]].rvalue.freeze_state_at)

                                    self.__actions[target_action_indices[target]].rvalue = self.__actions[target_action_indices[target]].rvalue.expression_update(
                                        expression=element,
                                        variable=element
                                    )
                
                        self.__actions[idx+n+1].rvalue = self.__actions[idx+n+1].rvalue.expression_update(
                            expression=self.__actions[target_action_indices[target]].rvalue,
                            variable=self.__actions[target_action_indices[target]].lvalue
                        )

                        self.__actions[idx+n+1].expansion = expand(self.__actions[idx+n+1].rvalue)

                        if target_action_indices[target] not in removed_actions:
                            removed_actions.append(target_action_indices[target])
                
                if action.lvalue == next_action.lvalue:
                    removed_actions.append(idx)
                    target += 1


        maps_to_delete = []

        for t in removed_actions:
            for i, m in enumerate(self.__map):
                if self.__actions[t].lvalue == m['action'].lvalue:
                    maps_to_delete.append(i)

        for t in reversed(sorted(set(removed_actions))):
            del self.__actions[t]

        for t in reversed(sorted(set(maps_to_delete))):
            del self.__map[t]

        return self.__variables, self.__actions, self.__map

    def convert(self):
        """
        The convert() method translates all the conversions to ACSL.
        :return:
        """
        return self.__conversions
    

class ARC(KnowledgeSharingChannel):
    """
    This is a channel class handles the knowledge sharing between the Action and Return components.
    """
    def __init__(self, actions: list, returns: list, vac_map: list):
        self.__actions = actions
        self.__returns = returns
        self.__vac_map = vac_map
        self.__conversions = []

    def overflow_check(self, component: Union[Action, Return]):
        """
        The overflow_check() is a method that handles overflow checks. Arithmetic operations is one of the cases
        where this method is used.
        :param component: The component to be checked: Action or Return.
        :return: Nothing, it deduces runtime overflow specifications for Action and Return blocks, then adds them
        into the conversion set.
        """
        target = ''
        items = []

        if isinstance(component, Action):
            items = [item for item in component.expansion if isinstance(item, (Variable, ID, FuncCall, Number))]
            target = component.rvalue.print() if len(component.rvalue.print()) < 20 else component.lvalue.print()

        elif isinstance(component, Return):
            items = [item for item in component.expansion if isinstance(item, (Variable, ID, FuncCall, Number))]
            target = component.output.print()

        if len(items) > 1:
            self.__conversions.append(
                    Conversion(conversion=f"requires INT_MIN < {target} < INT_MAX;", lib_imports='limits.h'))
        
    def build(self):
        """
        The build() method builds all the ARC contracts.
        :return:
        """ 
        for idx, ret in enumerate(self.__returns):
            
            if isinstance(ret.output, (Variable, ID)):
                dependent = False # This will check if the returned Variable or ID is used in another action.
                                  # If false, then remove the action where this variable is located.
                target_actions = []
                maps_to_delete = []

                for idy, action in enumerate(self.__actions):
                    if ret.output in action.expansion:
                        dependent = True

                    if action.lvalue == ret.output:
                        target_actions.append(idy)
                        maps_to_delete = [i for i, item in enumerate(self.__vac_map) if item['action'].lvalue == action.lvalue]
  
                for t in reversed(target_actions):
                    if self.__actions[t].condition == ret.condition or self.__actions[t].condition == ['ANY']:
                        self.__returns[idx].output = self.__actions[t].rvalue
                        self.__returns[idx].expansion = self.__actions[t].expansion

                    del self.__actions[t]

                for t in reversed(sorted(maps_to_delete)):
                    del self.__vac_map[t]
                
            self.overflow_check(self.__returns[idx])
        
        for action in self.__actions:
            self.overflow_check(action)

        return self.__actions, self.__returns
    
    def convert(self):
        """
        The convert() method translates all the conversions to ACSL.
        :return:
        """
        args = {'memory_separation': []}
        for i, mapping in enumerate(self.__vac_map):
            for conversion in mapping['variable'].convert():
                self.__conversions.append(conversion)

            for var in mapping['vars']:
                if isinstance(var, Variable):
                    arg = [mapping['variable'].variable.var_id(), var.var_id()]
                    if ((mapping['variable'].variable != var and mapping['variable'].variable.var_type == var.var_type
                            and var.var_type == 'pointer' and mapping['lvalue'] is True)
                            and set(arg) not in args['memory_separation']):

                        self.__conversions.append(Conversion(conversion=f"\\separated({mapping['variable'].variable.var_id()},"
                                                                    f" {var.var_id()});"))
                        args['memory_separation'].append(set(arg))
                
            for conversion in mapping['action'].convert():
                self.__conversions.append(conversion)

        return self.__conversions


class VRC(KnowledgeSharingChannel):
    """
    This is a channel class handles the knowledge sharing between the Var and Return components.
    """
    def __init__(self, variables: list, returns: list):
        self.__variables = variables
        self.__returns = returns
        self.__conversions = []


    def build(self):
        """
        The build() method builds all the VRC contracts.
        :return:
        """
        flag = False
        priority_return = None
        for idx, ret in enumerate(self.__returns):
            if self.__returns[idx].condition == ['ANY'] and not flag:
                flag = True
                priority_return = idx

            if flag and priority_return < idx:
                del self.__returns[idx]

        for idx, ret in enumerate(self.__returns):
            for var in self.__variables:
                ConditionProcessor(var.variable, traversed_condition=ret.condition)
                if isinstance(ret.output, Expr):
                    self.__returns[idx].output = self.__returns[idx].output.variable_update(var.variable)
            

    def convert(self):
        """
        The convert() method translates all the conversions to ACSL.
        :return:
        """
        for ret in self.__returns:
            for conversion in ret.convert():
                self.__conversions.append(conversion)

        return self.__conversions


class Contracts:
    """
    This is a base class for contracts.
    """
    def __init__(self, contracts: dict):
        self.__contracts = contracts

    def string(self):
        """
        The string() method returns a string version of the contracts.
        :return:
        """
        out = ''
        if 'pre_conditions' in self.__contracts.keys():
            if len(self.__contracts['pre_conditions']) == 0:
                out += 'requires \\true;\n'
            else:
                for item in self.__contracts['pre_conditions']:
                    out += f'{item}\n'
        if self.__contracts['misc_contracts']:
            for item in self.__contracts['misc_contracts']:
                out += f'{item}\n'
        if 'assigns_contracts' in self.__contracts.keys():
            if len(self.__contracts['assigns_contracts']) == 0:
                out += 'assigns \\nothing;\n'
            else:
                for item in self.__contracts['assigns_contracts']:
                    out += f'{item}\n'
        if 'post_conditions' in self.__contracts.keys():
            if len(self.__contracts['post_conditions']) == 0:
                out += 'ensures \\true;\n'
            else:
                for item in self.__contracts['post_conditions']:
                    out += f'{item}\n'

        return '/*@\n' + out.strip('\n') + '\n*/'
    
    def get_imports(self):
        """
        get_imports() is used to retrieve the included libraries. 
        """
        out = ''
        if self.__contracts['imports']:
            for item in self.__contracts['imports']:
                out += f'#include <{item}>\n'

        return out.strip('\n')


class Pyramid:
    """
    Pyramid is the symbolic engine that converts an NAR (Nectron Abstract Representation) source file into ACSL contracts.
    """
    def __init__(self, nar_grammar=None):

        self.__var_block_parser = VarParser()
        self.__action_block_parser = ActionParser()
        self.__return_block_parser = ReturnParser()

        self.__vac = None
        self.__arc = None
        self.__vrc = None

        grammar = nar_grammar if nar_grammar is not None else './nar_grammar/nar.lark'

        if os.path.exists(grammar):
            with open(grammar, 'r') as fp:
                self.__nar_grammar = fp.read()
        else:
            raise UnspecifiedNARGrammarFile

        self.__source_parser = Lark(self.__nar_grammar).parser

        self.__nar_source = None

    def read_nar_from_file(self, nar_source_path: str):
        """
        The read_nar_from_file() method is used to read an NAR script from a file. The file must have a .nar file
        extension.
        :param nar_source_path: The NAR file path.
        :return: Nothing, it stores the script in the Pyramid object's memory.
        """

        if nar_source_path.endswith('.nar') and os.path.exists(nar_source_path):
            with open(nar_source_path, 'r') as fp:
                self.__nar_source = self.__syntax_fixes(fp.read())
        else:
            raise UnspecifiedNARSourceFile

        return True

    @staticmethod
    def __syntax_fixes(nar: str):
        """
        The __syntax_fixes() method is used internally to systematically correct certain syntactic errors of an NAR
        script.
        :param nar: The NAR script.
        :return: It returns the corrected NAR script.
        """
        if nar.find('var:') == -1:
            raise NonCompilableNAR
        elif nar.find('action:') == -1:
            ret_idx = nar.find('return:')
            if ret_idx != -1:
                nar = nar[:ret_idx] + 'action:\n\tNone condition ANY\n' + nar[ret_idx:]
            else:
                nar = nar[:] + 'action:\n\tNone condition ANY\nreturn:\n\tNone condition ANY'
                nar = nar.strip('\n')
        elif nar.find('return:') == -1:
            nar = nar[:] + 'return:\n\tNone condition ANY'
            nar = nar.strip('\n')

        nar.replace('True', 'true')
        nar.replace('False', 'false')

        new_nar = '\n'.join([line for line in nar.splitlines() if line.find("\"") == -1])

        return new_nar

    def read_nar_from_generated(self, generated_nar: str):
        """
        The read_nar_from_generated() method is used to read the NAR script directly from the NAR Generator model.
        :param generated_nar: The generated nar script.
        :return: Nothing, it stores the script in the Pyramid object's memory.
        """
        self.__nar_source = self.__syntax_fixes(generated_nar)

    @staticmethod
    def __build_contracts(contract_sets: list):
        """
        The __build_contracts() method is used internally to build contracts (i.e. to generate ACSL) for the whole NAR
        script.
        :param contract_sets: The contract set of every Knowledge-Sharing Channel.
        :return: A Contracts object that encapsulates all the generated contracts.
        """
        contracts = {'imports': set(), 'pre_conditions': [], 'post_conditions': [],
                     'misc_contracts': [], 'assigns_contracts': []}
        for cs in contract_sets:
            for contract in cs:
                if 'requires' in contract.conversion:
                    if contract.conversion not in contracts['pre_conditions']:
                        contracts['pre_conditions'].append(contract.conversion)
                elif 'ensures' in contract.conversion:
                    if contract.conversion not in contracts['post_conditions']:
                        contracts['post_conditions'].append(contract.conversion)
                elif '\\separated' in contract.conversion:
                    if contract.conversion not in contracts['misc_contracts']:
                        contracts['misc_contracts'].append(contract.conversion)
                elif 'assigns' in contract.conversion:
                    if contract.conversion not in contracts['assigns_contracts']:
                        contracts['assigns_contracts'].append(contract.conversion)

                if len(contract.lib_imports) > 0:
                    contracts['imports'].add(contract.lib_imports)

        return Contracts(contracts=contracts)

    def compile(self) -> Contracts:
        """
        The compile() method is the main compilation method, it is used to convert an NAR script into ACSL contracts.
        :return: a Contracts object.
        """
        if self.__nar_source is None:
            raise UnspecifiedNARSourceFile
        try:
            parsed_file = self.__source_parser.parse(self.__nar_source)
        except (exceptions.UnexpectedCharacters or exceptions.MissingVariableError
                or exceptions.GrammarError):
            raise NonCompilableNAR

        self.__var_block_parser.transform(parsed_file.children[0])
        self.__action_block_parser.transform(parsed_file.children[1])
        self.__return_block_parser.transform(parsed_file.children[2])
        
        self.__vac = VAC(self.__var_block_parser.vars, self.__action_block_parser.actions)
        variables, actions, vac_map = self.__vac.build()
        vac_conversions = self.__vac.convert()

        self.__arc = ARC(actions, self.__return_block_parser.returns, vac_map)
        actions, returns = self.__arc.build()
        arc_conversions = self.__arc.convert()

        self.__vrc = VRC(variables, returns)
        self.__vrc.build()
        vrc_conversions = self.__vrc.convert()

        return self.__build_contracts([arc_conversions, vac_conversions, vrc_conversions])
