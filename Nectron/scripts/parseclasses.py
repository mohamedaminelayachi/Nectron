
try:
    from dataclasses import dataclass
    from typing import Union, Any
except ImportError:
    raise ImportError("You seem to have missed some dependencies. Make sure to check the requirements.")


class Expr:
    """
    The Expr class is the superclass for all NAR expressions, such as: variables, mathematical expressions, etc.
    """
    def __init__(self):
        self.children = []
        self.freeze_state_at = None

    def evaluate(self):
        """
        :return: The evaluated version of the expression. Note: not all expressions can be evaluated.
        """
        raise NotImplementedError

    def variable_update(self, variable, share_old_flag=False, freeze_state=False):
        """
        :param: variable: it takes a new Variable structure and updates every occurrence of the old one with the new one.
        It is part of the Knowledge-Sharing Mechanism.
        :param: share_old_flag: a parameter by which we control whether we want the old predicate flag to be shared or not.
        This is useful in cases where the state of the Variable/ID needs to be frozen at a particular action or not.
        :param: freeze_state: a parameter by which we decide whether we want to take the state of an expression at a particular
        action, in other words, it will freeze the state (attributes) of all variables in the expression. This is useful in 
        variable and action reduction.
        :return: Nothing.
        """
        two_arg_expressions = (Add, Sub, Mul, Div, Modulo, BitwiseAND, BitwiseLeftShift, BitwiseOR, BitwiseRightShift, BitwiseXOR)
        one_arg_expressions = (Neg, Pos, BitwiseNOT)

        if isinstance(self, Variable) and isinstance(variable, Variable) and variable == self:

            self.var_type = variable.var_type
            self.write_permission = variable.write_permission
            if share_old_flag:
                self.old_predicate_flag = variable.old_predicate_flag

        elif isinstance(self, ID) and isinstance(variable, Variable) and self.name == variable.var_id():
            var = Variable(var_id=self.name, var_type=variable.var_type, write_permission=variable.write_permission)
            if share_old_flag:
                var.old_predicate_flag = variable.old_predicate_flag
            if freeze_state:
                var.freeze_state_at = variable.freeze_state_at

            return var

        elif isinstance(self, ID) and isinstance(variable, ID) and self.name == variable.name:
            var = Variable(var_id=self.name, var_type='integer', write_permission=variable.write_permission)
            if share_old_flag:
                var.old_predicate_flag = variable.old_predicate_flag
            if freeze_state:
                var.freeze_state_at = variable.freeze_state_at

            return var

        elif isinstance(self, two_arg_expressions):
            if isinstance(self.left, Expr) and not isinstance(self.left, (Number, Bool)):
                self.left = self.left.variable_update(variable, share_old_flag, freeze_state)

            if isinstance(self.right, Expr) and not isinstance(self.right, (Number, Bool)):
                self.right = self.right.variable_update(variable, share_old_flag, freeze_state)

        elif isinstance(self, one_arg_expressions):
            if isinstance(self.expr, Expr) and not isinstance(self.expr, (Number, Bool)):
                self.expr = self.expr.variable_update(variable, share_old_flag, freeze_state)

        elif isinstance(self, FuncCall):
            for i, arg in enumerate(self.args):
                if isinstance(arg, Expr):
                    self.args[i] = self.args[i].variable_update(variable, share_old_flag, freeze_state)

        elif isinstance(variable, Number) and variable == self:
            self.value = variable.value

        elif isinstance(self, Bool):
            return None

        if freeze_state:
                self.freeze_state_at = variable.freeze_state_at

        return self
        

    def expression_update(self, expression, variable):
        """
        :param: expression: it takes the expression that a variable holds in a previous action and inject it in the current 
        action's expression. This reduces the number of used variables.
        :param: variable: the variable that holds the expression.
        :return: Nothing.
        """
        if isinstance(expression, Expr) and isinstance(variable, (Variable, ID)):
            
            left_right_expr = (Add, Sub, Mul, Modulo, Div, BitwiseAND, BitwiseOR, 
                               BitwiseXOR, BitwiseLeftShift, BitwiseRightShift)
            unary_expr = (Pos, Neg, BitwiseNOT)
            
            
            if isinstance(self, left_right_expr):
                if variable == self.left and self.left.freeze_state_at > expression.freeze_state_at:
                    self.left = expression
                    self.children[0] = expression
                elif self.left.does_variable_exist(variable):
                    self.left = self.left.expression_update(expression=expression, variable=variable)

                if variable == self.right and self.right.freeze_state_at > expression.freeze_state_at:
                    self.right = expression
                    self.children[2] = expression
                elif self.right.does_variable_exist(variable):
                    self.right = self.right.expression_update(expression=expression, variable=variable)
                    
            elif isinstance(self, unary_expr) and self.expr.freeze_state_at > expression.freeze_state_at:
                if variable == self.expr:
                    self.expr = expression
                    self.children[1] = expression
                elif self.expr.does_variable_exist(variable):
                    self.expr = self.expr.expression_update(expression=expression, variable=variable)

            elif isinstance(self, FuncCall):
                for i, arg in enumerate(self.args):
                    if isinstance(arg, Expr) and arg.freeze_state_at > expression.freeze_state_at:
                        self.args[i] = self.args[i].expression_update(expression=expression, variable=variable)

            elif isinstance(self, (Variable, ID)) and self.freeze_state_at > expression.freeze_state_at:
                return expression

        return self

    def freeze(self, freeze_index):
        left_right_expr = (Add, Sub, Mul, Modulo, Div, BitwiseAND, BitwiseOR, 
                           BitwiseXOR, BitwiseLeftShift, BitwiseRightShift)
        unary_expr = (Pos, Neg, BitwiseNOT)

        self.freeze_state_at = freeze_index
        
        if isinstance(self, left_right_expr):
            self.left.freeze(freeze_index)
            self.right.freeze(freeze_index)

        elif isinstance(self, unary_expr):
            self.expr.freeze(freeze_index)

        elif isinstance(self, FuncCall):
            for i, arg in enumerate(self.args):
                if isinstance(arg, Expr):
                    self.args[i].freeze(freeze_index)

    def does_variable_exist(self, variable):
        occurrences = self.find(variable, [])

        if len(occurrences) > 0:
            exists = False
        else:
            exists = True

        return exists
    
    def find(self, variable, occurrences: list):
        if not self.children:
            if self == variable:
                occurrences.append(self)

            elif isinstance(self, FuncCall):
                for arg in self.args:
                    if isinstance(arg, Expr):
                        arg.find(variable, occurrences)

        for item in self.children:
            if item == variable:
                occurrences.append(item)
            elif isinstance(item, Expr):
                item.find(variable, occurrences)

        return occurrences
            
    def print(self):
        """
        :return: A string version of the expression.
        """
        raise NotImplementedError


class ID(Expr):
    """
    ID is the structure class of IDs.
    """
    def __init__(self, name, write_permission=False):
        super().__init__()
        self.name = name
        self.children = []
        self.write_permission = write_permission
        self.old_predicate_flag = False

    def print(self):
        if self.old_predicate_flag:
            return f'\\old({self.name})'
        
        return str(self.name)
    
    def evaluate(self):
        return 0

    def __eq__(self, other):
        if isinstance(other, ID):
            return self.name == other.name
        elif isinstance(other, Variable):
            return self.name == other.var_id()
        else:
            return False


class Variable(Expr):
    """
    Variable is the structure class of variables.
    """
    def __init__(self, var_id, var_type, write_permission=False):
        super().__init__()
        self.__var_id = var_id
        self.var_type = var_type
        self.write_permission = write_permission
        self.old_predicate_flag = False
        self.freeze_state_at = None

    def var_id(self) -> str:
        """
        :return: The variable's identifier (i.e. name).
        """
        return str(self.__var_id)

    def print(self):
        if self.old_predicate_flag:
            if self.var_type == 'pointer':
                return f"\\old(*{self.__var_id})"
            else:
                return f'\\old({self.__var_id})'
        else:
            if self.var_type == 'pointer':
                return f"*{self.__var_id}"
            else:
                return str(self.__var_id)
    
    def evaluate(self):
        return 0

    def __eq__(self, other):
        if isinstance(other, Variable):
            return self.var_id() == other.var_id()
        elif isinstance(other, ID):
            return self.var_id() == other.name
        else:
            return False


class Bool(Expr):
    """
    Bool is the structure class of boolean expressions.
    """
    def __init__(self, boolean):
        super().__init__()
        self.boolean = boolean
        self.children = []

    def evaluate(self):
        return 0

    def print(self):
        return f"\\{self.boolean}"


class Number(Expr):
    """
    Number is the structure class of numerical expressions.
    """
    def __init__(self, value):
        super().__init__()
        self.value = float(value)
        self.children = []

    def evaluate(self):
        return self.value

    def print(self):
        if self.value == int(self.value):
            return str(int(self.value))
        else:
            return str(self.value)
        
    def __eq__(self, other):
        if isinstance(other, Number):
            return self.evaluate() == other.evaluate()
       

# Arithmetic Operations
class Add(Expr):
    """
    Add is the structure class of addition operations.
    """
    def __init__(self, left, right):
        super().__init__()
        self.left = left
        self.right = right
        self.children = [left, '+', right]

    def evaluate(self):
        return self.left.evaluate() + self.right.evaluate()

    def print(self):
        out = ''
        if isinstance(self.left, str):
            out += f"({self.left} + "
        else:
            out += f"({self.left.print()} + "

        if isinstance(self.right, str):
            out += f"{self.right}"
        else:
            out += f"{self.right.print()}"

        out = out.strip() + ')'
        return out


class Sub(Expr):
    """
    Sub is the structure class of subtraction operations.
    """
    def __init__(self, left, right):
        super().__init__()
        self.left = left
        self.right = right
        self.children = [left, '-', right]

    def evaluate(self):
        return self.left.evaluate() - self.right.evaluate()

    def print(self):
        out = ''
        if isinstance(self.left, str):
            out += f"({self.left} - "
        else:
            out += f"({self.left.print()} - "

        if isinstance(self.right, str):
            out += f"{self.right}"
        else:
            out += f"{self.right.print()}"

        out = out.strip() + ')'
        return out


class Mul(Expr):
    """
    Mul is the structure class of multiplication operations.
    """
    def __init__(self, left, right):
        super().__init__()
        self.left = left
        self.right = right
        self.children = [left, '*', right]

    def evaluate(self):
        return self.left.evaluate() * self.right.evaluate()

    def print(self):
        out = ''
        if isinstance(self.left, str):
            out += f"({self.left} * "
        else:
            out += f"({self.left.print()} * "

        if isinstance(self.right, str):
            out += f"{self.right}"
        else:
            out += f"{self.right.print()}"
        
        out = out.strip() + ')'
        return out


class Modulo(Expr):
    """
    Modulo is the structure class of modulo operations.
    """
    def __init__(self, left, right):
        super().__init__()
        self.left = left
        self.right = right
        self.children = [left, '%', right]

    def evaluate(self):
        return self.left.evaluate() % self.right.evaluate()

    def print(self):
        out = ''
        if isinstance(self.left, str):
            out += f"({self.left} % "
        else:
            out += f"({self.left.print()} % "

        if isinstance(self.right, str):
            out += f"{self.right}"
        else:
            out += f"{self.right.print()}"
        out = out.strip() + ')'
        return out


class Div(Expr):
    """
    Div is the structure class of division operations.
    """
    def __init__(self, left, right):
        super().__init__()
        self.left = left
        self.right = right
        self.children = [left, '/', right]

    def evaluate(self):
        return self.left.evaluate() / self.right.evaluate()

    def print(self):
        out = ''
        if isinstance(self.left, str):
            out += f"({self.left} / "
        else:
            out += f"({self.left.print()} / "

        if isinstance(self.right, str):
            out += f"{self.right}"
        else:
            out += f"{self.right.print()}"
        out = out.strip() + ')'
        return out


class Neg(Expr):
    """
    Neg is the structure class of negation operations.
    """
    def __init__(self, expr):
        super().__init__()
        self.expr = expr
        self.children = ['-', expr]

    def evaluate(self):
        return -self.expr.evaluate()

    def print(self):
        if isinstance(self.expr, str):
            return f"(-{self.expr})"
        else:
            return f"(-{self.expr.print()})"


class Pos(Expr):
    """
    Pos is the structure class of positivity operations (i.e. optional positivity sign behind a number or a variable).
    """
    def __init__(self, expr):
        super().__init__()
        self.expr = expr
        self.children = ['+', expr]

    def evaluate(self):
        return +self.expr.evaluate()

    def print(self):
        if isinstance(self.expr, str):
            return f"(+{self.expr})"
        else:
            return f"(+{self.expr.print()})"


# Bitwise Operations
class BitwiseNOT(Expr):
    """
    BitwiseNOT is the structure class of bitwise NOT operations.
    """
    def __init__(self, expr):
        super().__init__()
        self.expr = expr
        self.children = ['~', expr]

    def evaluate(self):
        return ~self.expr.evaluate()
    
    def print(self):
        if isinstance(self.expr, str):
            return f"(~{self.expr})"
        else:
            return f"(~{self.expr.print()})"


class BitwiseAND(Expr):
    """
    BitwiseAND is the structure class of bitwise AND operations.
    """
    def __init__(self, left, right):
        super().__init__()
        self.left = left
        self.right = right
        self.children = [left, '&', right]

    def evaluate(self):
        return self.left.evaluate() & self.right.evaluate()

    def print(self):
        out = ''
        if isinstance(self.left, str):
            out += f"({self.left} & "
        else:
            out += f"({self.left.print()} & "

        if isinstance(self.right, str):
            out += f"{self.right}"
        else:
            out += f"{self.right.print()}"
        
        out = out.strip() + ')'
        return out


class BitwiseOR(Expr):
    """
    BitwiseOR is the structure class of bitwise OR operations.
    """
    def __init__(self, left, right):
        super().__init__()
        self.left = left
        self.right = right
        self.children = [left, '|', right]

    def evaluate(self):
        return self.left.evaluate() | self.right.evaluate()

    def print(self):
        out = ''
        if isinstance(self.left, str):
            out += f"({self.left} | "
        else:
            out += f"({self.left.print()} | "

        if isinstance(self.right, str):
            out += f"{self.right}"
        else:
            out += f"{self.right.print()}"
        out = out.strip() + ')'
        return out


class BitwiseLeftShift(Expr):
    """
    BitwiseLeftShift is the structure class of bitwise Left Shift operations.
    """
    def __init__(self, left, right):
        super().__init__()
        self.left = left
        self.right = right
        self.children = [left, '<<', right]

    def evaluate(self):
        return self.left.evaluate() << self.right.evaluate()

    def print(self):
        out = ''
        if isinstance(self.left, str):
            out += f"({self.left} << "
        else:
            out += f"({self.left.print()} << "

        if isinstance(self.right, str):
            out += f"{self.right}"
        else:
            out += f"{self.right.print()}"
        
        out = out.strip() + ')'
        return out


class BitwiseRightShift(Expr):
    """
    BitwiseRightShift is the structure class of bitwise Right Shift operations.
    """
    def __init__(self, left, right):
        super().__init__()
        self.left = left
        self.right = right
        self.children = [left, '>>', right]

    def evaluate(self):
        return self.left.evaluate() >> self.right.evaluate()

    def print(self):
        out = ''
        if isinstance(self.left, str):
            out += f"({self.left} >> "
        else:
            out += f"({self.left.print()} >> "

        if isinstance(self.right, str):
            out += f"{self.right}"
        else:
            out += f"{self.right.print()}"
        
        out = out.strip() + ')'
        return out


class BitwiseXOR(Expr):
    """
    BitwiseXOR is the structure class of bitwise XOR operations.
    """
    def __init__(self, left, right):
        super().__init__()
        self.left = left
        self.right = right
        self.children = [left, '^', right]

    def evaluate(self):
        return self.left.evaluate() ^ self.right.evaluate()

    def print(self):
        out = ''
        if isinstance(self.left, str):
            out += f"({self.left} ^ "
        else:
            out += f"({self.left.print()} ^ "

        if isinstance(self.right, str):
            out += f"{self.right}"
        else:
            out += f"{self.right.print()}"
        
        out = out.strip() + ')'
        return out


class FuncCall(Expr):
    """
    FuncCall is the structure class of function calls.
    """
    def __init__(self, name, args):
        super().__init__()
        self.name = name
        self.args = args
        self.children = []

    def evaluate(self):
        pass

    def print_args(self):
        return ' '.join(arg.print() for arg in self.args).strip()

    def print(self):
        args_str = ", ".join(arg.print() for arg in self.args)
        return f"{self.name.print()}({args_str})"


@dataclass
class Block:
    """
    This is a base class for Var, Action, and Return blocks of NAR.
    """
    def build(self):
        raise NotImplementedError

    def convert(self):
        raise NotImplementedError


@dataclass
class Conversion:
    """
    Conversion is the structure class for ACSL contracts. It stores the contracts converted from NAR to ACSL.
    """
    conversion: str
    lib_imports: str = ''

    def __eq__(self, other):
        if isinstance(other, Conversion):
            return self.conversion == other.conversion
        else:
            return False

    def __hash__(self):
        return hash(self.conversion)

    def __str__(self):
        return self.conversion


@dataclass
class Function:
    """
    Function is the structure class for function used in NAR. It stores the function's identifier, arguments, and
    return type.
    """
    func_id: str
    arguments: list[str]
    type: str = None

    def reconstruct(self):
        """
        :return: A string of the function call.
        """
        out = f'{self.func_id}('
        out += ','.join(self.arguments)
        out += ')'
        return out


@dataclass
class MathExpression:
    """
    MathExpression is the base class for mathematical expressions.
    """
    expr: list
    sign: str = '+'

    def reconstruct(self):
        """
        :return: A string for the expressions.
        """
        out = ''
        if isinstance(self.expr, list) and isinstance(self.expr[0], list) and self.expr[0][0] == '-':
            out = '-'
        else:
            out = ''
        if isinstance(self.expr, MathExpression):
            out += f'{self.expr.reconstruct()}'
        elif isinstance(self.expr, list):
            for expr in self.expr:
                if isinstance(expr, Function):
                    out += f'{expr.reconstruct()}'
                elif isinstance(expr, MathExpression):
                    out += f'({expr.reconstruct()})'
                else:
                    out += f'{expr}'
                out += ' '
        return out.strip()


@dataclass
class Expression:
    """
    Expression is a deprecated class that was used to store expressions, which was replaced with Expr.
    """
    exp: list
    sign: str = '+'
    bitwise_not: bool = False

    def reconstruct(self):
        out = '~' if self.bitwise_not else ''
        if len(self.exp) == 1:
            for x in self.exp[1]:
                pass
        for item in self.exp:
            if isinstance(item, MathExpression):
                out += f'{item.reconstruct()}'
            elif isinstance(item, str):
                out += f'{item}'

            out += ' '

        return out.strip()


@dataclass
class Comparison:
    """
    Comparison is the base class for any comparisons inside a condition. It stores left and right values of
    the comparison, as well as the comparison operator (e.g. <=, ==, etc.)
    """
    lvalue: Any
    rvalue: Any
    comp_op: str

    def inject_variable(self, variable: Variable):
        """
        The inject_variable() method takes in a new Variable structure and updates every occurrence of the old one
        inside the current comparison with the new one.
        :param variable: The new Variable structure.
        :return: Nothing, it updates the variable inside the left and right values of the comparison.
        """
        if isinstance(self.lvalue, (Variable, ID)):
            self.lvalue = variable if self.lvalue == variable else self.lvalue
        elif isinstance(self.lvalue, Expr) and not isinstance(self.lvalue, (Number, Bool, FuncCall)):
            self.lvalue = self.lvalue.variable_update(variable)
        if isinstance(self.rvalue, (Variable, ID)):
            self.rvalue = variable if self.rvalue == variable else self.rvalue
        elif isinstance(self.rvalue, Expr) and not isinstance(self.rvalue, (Number, Bool, FuncCall)):
            self.rvalue = self.rvalue.variable_update(variable)

    def reconstruct(self):
        """
        :return: A string version of the comparison.
        """
        out = ''
        if isinstance(self.lvalue, Expr):
            left = self.lvalue.print()
            if self.comp_op == 'is':
                out += f"{left} == "
            else:
                out += f"{left} {self.comp_op} "
        elif isinstance(self.lvalue, str):
            out += f"{self.lvalue} {self.comp_op} "
        if isinstance(self.rvalue, Expr):
            right = self.rvalue.print()
            out += f"{right}"
        elif isinstance(self.rvalue, str):
            out += f"{self.rvalue}"

        out = '(' + out.strip() + ')'
        return out

    def does_variable_exist(self, variable):
        if isinstance(self.lvalue, Expr):
            return self.lvalue.does_variable_exist(variable)
        elif isinstance(self.rvalue, Expr):
            return self.rvalue.does_variable_exist(variable)

        return False
        
    def get_attributes(self):
        """
        :return: The left and right values of the comparison, as well as its operator.
        """
        return self.lvalue, self.rvalue, self.comp_op
    
    def __eq__(self, other):
        if isinstance(other, Comparison):
            lvalue_check = (self.lvalue == other.lvalue)
            rvalue_check = (self.rvalue == other.rvalue)
            comp_op_check = (self.comp_op == other.comp_op)
            if lvalue_check and rvalue_check and comp_op_check:
                return True
            return False
        return False

def traverse(__list__):
    """
    The traverse() function is a utility function that helps in traversing a list recursively and getting its elements.
    :param __list__: A list.
    :return:
    """
    if not isinstance(__list__, list):
        yield __list__
    else:
        for e in __list__:
            yield from traverse(e)


@dataclass
class Condition:
    """
    Condition is the base class for conditions that are used with actions and returns.
    """
    negation: bool
    condition: list[Any]

    def reconstruct(self):
        """
        :return: A string version of the condition.
        """
        out = ''

        conditions = traverse(self.condition)

        for cond in conditions:
            if isinstance(cond, Comparison):
                out += f"{cond.reconstruct()}"
            elif isinstance(cond, Condition):
                out += f"{cond.reconstruct()}"
            elif isinstance(cond, str):
                if cond == 'and':
                    out += f"&&"
                elif cond == 'or':
                    out += f"||"
                else:
                    out += f"{cond}"

            out += ' '

        
        if self.negation:
            out = '!(' + out.strip() + ')'
        else:
            out = out.strip()

        return out

    def does_variable_exist(self, variable: Union[Variable, ID]):
        exists = False
        flat_list = flatten_condition([], self.condition)
        for item in flat_list:
            if isinstance(item, Comparison) and not exists:
                exists = item.does_variable_exist(variable) 

        return exists

    def __eq__(self, other):
        flag = False
        if isinstance(other, Condition):
            if self.condition == other.condition:
                flag = True
        return flag

def flatten_condition(flat_list: list, condition):
    if isinstance(condition, Condition):
        return flatten_condition(flat_list, condition.condition)
    elif isinstance(condition, Comparison):
        flat_list.append(condition)
    elif isinstance(condition, list):
        sublist = []
        for item in condition:
            flatten_condition(sublist, item)
        for item in sublist:
            flat_list.append(item)

    return flat_list
    
def expand(root) -> list:
    """
    The expand() function flattens a multidimensional list into 1D.
    :param root: The root node of the expansion (e.g. an NAR expression)
    :return: A flattened list.
    """
    answer = []
    expandUtil(root, answer)
    return answer


def expandUtil(root, answer):
    """
    The expandUtil() is a recursive utility function that helps in the list flattening process.
    :param root: the current root node of expansion.
    :param answer: the global list.
    :return: A flattened list.
    """
    if not root.children:
        answer.append(root)
        return root
    elif len(root.children) == 2:
        answer.append(root.children[0])
        expandUtil(root.children[1], answer)
    elif len(root.children) == 3:
        expandUtil(root.children[0], answer)
        answer.append(root.children[1])
        expandUtil(root.children[2], answer)


class Var(Block):
    """
    The Var class implements methods to convert the NAR Var block into corresponding ACSL contracts.
    """
    def __init__(self, variable: Variable):
        self.variable = variable
        self.var_conversions = []

    def convert(self):
        """
        The convert() method converts the Var block into ACSL contracts.
        :return: list of ACSL contracts as Conversion objects.
        """
        if self.variable.var_type == 'pointer':
            if self.variable.write_permission:
                self.var_conversions.append(Conversion(
                    conversion=f"requires \\valid({self.variable.var_id()});",
                    lib_imports=''))
            else:
                self.var_conversions.append(Conversion(
                    conversion=f"requires \\valid_read({self.variable.var_id()});",
                    lib_imports=''))

        return self.var_conversions

    def __str__(self):
        return (f"id={self.variable.var_id()}, type={self.variable.var_type},"
                f" write_permission={self.variable.write_permission}," 
                f" old_predicate_flag={self.variable.old_predicate_flag}")


class Action(Block):
    """
    The Action class implements methods to convert the NAR Var block into corresponding ACSL contracts.
    """
    def __init__(self, lvalue: Any, rvalue: Any, condition: list):
        self.lvalue = lvalue
        self.rvalue = rvalue
        self.condition = condition
        self.action_conversions = []
        self.expansion = []

        if isinstance(self.lvalue, ID):
            self.lvalue = Variable(var_id=self.lvalue.name, var_type='integer', write_permission=True)

        self.expansion = expand(self.rvalue)

        for i, item in enumerate(self.expansion):
            if isinstance(item, ID):
                self.expansion[i] = Variable(var_id=item.name, var_type='integer', write_permission=False)

    def convert(self):
        """
            The convert() method converts the Action block into ACSL contracts.
            :return: list of ACSL contracts as Conversion objects.
        """        
        if self.condition[0] == 'ANY':
            self.action_conversions.append(Conversion(
                conversion=f"ensures {self.lvalue.print()} == {self.rvalue.print()};"
            ))
        else:
            self.action_conversions.append(Conversion(
                conversion=f"ensures {self.str_condition()} ==> {self.lvalue.print()} == {self.rvalue.print()};"
            ))

        self.action_conversions.append(Conversion(
                conversion=f"assigns {self.lvalue.print()};"
        ))

        return self.action_conversions

    def __str__(self):
        return f"lvalue={self.lvalue}, rvalue={self.rvalue}, condition={self.condition}"

    def str_condition(self):
        """
        :return: a string version of the condition.
        """
        out = ''
        for condition in self.condition:
            if isinstance(condition, str):
                if condition == 'and':
                    out += f"&&"
                elif condition == 'or':
                    out += f"||"
                else:
                    out += f"{condition}"
            elif isinstance(condition, Expr):
                out += f"{condition.print()}"
            elif isinstance(condition, Condition):
                out += f"{condition.reconstruct()}"

            out += ' '

        out = out.strip()

        return out

    def opslen(self):
        """
        :return: Number of operations in the action's rvalue.
        """
        return sum([1 for item in self.expansion if isinstance(item, str)])

class Return(Block):

    def __init__(self, output: Any, condition: list):
        self.output = output
        self.condition = condition
        self.return_conversions = []
        self.expansion = expand(output)

    def convert(self):
        """
            The convert() method converts the Return block into ACSL contracts.
            :return: list of ACSL contracts as Conversion objects.
        """
        if len(self.condition) == 1 and self.condition[0] == 'ANY':
            output = self.output
            if isinstance(self.output, Expr):
                output = self.output.print()
            elif isinstance(self.output, str):
                output = self.output
            if output != 'None':
                self.return_conversions.append(Conversion(
                    conversion=f"ensures \\result == {output};"
                ))
        else:
            output = self.output
            if isinstance(self.output, Expr):
                output = self.output.print()
            elif isinstance(self.output, str):
                output = self.output
            self.return_conversions.append(Conversion(
                conversion=f"ensures {self.str_condition()} ==> \\result == {output};"
            ))

        return self.return_conversions

    def str_condition(self):
        """
        :return: A string version of the condition.
        """
        out = ''
        for condition in self.condition:
            if isinstance(condition, str):
                if condition == 'and':
                    out += f"&&"
                elif condition == 'or':
                    out += f"||"
                else:
                    out += f"{condition}"
            elif isinstance(condition, Expr):
                out += f"{condition.print()} condition"
            elif isinstance(condition, Condition):
                out += f"{condition.reconstruct()}"

            out += ' '

        out = out.strip()

        return out

    def __str__(self):
        return f"output={self.output}, condition={self.condition}"


class Builder:
    """
    The Builder class implements methods to assign structure classes with respect to the provided expression.
    """
    @staticmethod
    def build_function(function_list: list):
        """
        The build_function() creates a Function structure class for a function call.
        :param function_list: Items of the function call (i.e. id, arguments)
        :return: Function structure class.
        """
        function_arguments = []
        if len(function_list) == 1:
            function_id = function_list[0][0]
            for arg in function_list[0][1]:
                if isinstance(arg, list):
                    for item in arg:
                        if isinstance(item, MathExpression):
                            function_arguments.append(item.reconstruct())
                        else:
                            function_arguments.append(item)
                elif isinstance(arg, MathExpression):
                    function_arguments.append(arg.reconstruct())
                else:
                    function_arguments.append(arg)

        elif len(function_list) == 2:
            function_id = function_list[1][0]
            for arg in function_list[1][1]:
                if isinstance(arg, list):
                    for item in arg:
                        if isinstance(item, MathExpression):
                            function_arguments.append(item.reconstruct())
                        else:
                            function_arguments.append(item)
                elif isinstance(arg, MathExpression):
                    function_arguments.append(arg.reconstruct())
                else:
                    function_arguments.append(arg)
        else:
            raise Exception(f'Cannot build function {function_list}')

        return Function(func_id=function_id, arguments=function_arguments)

    @staticmethod
    def build_comparison(comparison: list):
        """
        The build_comparison() creates a Comparison structure class for a provided comparison statement inside
        a condition.
        :param comparison: Items of the comparison statement (i.e. lvalue, rvalue, comparison operator).
        :return: Comparison structure class.
        """
        lvalue = comparison[0]
        comparison_operator = comparison[1]
        rvalue = comparison[2]
        return Comparison(lvalue=lvalue, rvalue=rvalue, comp_op=comparison_operator)

    @staticmethod
    def build_condition(condition: list):
        """
        The build_condition() creates a Condition structure class for a provided condition statement.
        :param condition: Items of the condition statement.
        :return: Condition structure class.
        """
        if len(condition) == 1:
            return Condition(negation=False, condition=condition[0])
        if len(condition) == 2:
            if condition[0][0] == '!':
                return Condition(negation=True, condition=condition[1])

    @staticmethod
    def build_math_expression(math_expression: list):
        """
        The build_math_expression() creates a MathExpression structure class for a provided expression.
        (NOTE: the method is deprecated and not used)
        :param math_expression: Items of the mathematical expression.
        :return: MathExpression structure class.
        """
        if len(math_expression) == 2:
            return MathExpression(expr=math_expression[1], sign=math_expression[0])

        return MathExpression(expr=math_expression)


