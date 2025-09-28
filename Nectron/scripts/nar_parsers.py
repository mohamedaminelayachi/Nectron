try:
    from lark import Lark
    from lark import Transformer, v_args
    from .parseclasses import *
except ImportError:
    raise ImportError("You seem to have missed some dependencies. Make sure to check the requirements.")


class Utility(Transformer):
    """
    The Utility class inherits the Lark's Transformer methods to parse NAR syntax. To facilitate the parsing pipeline,
    this class implements methods to parse each token according to the NAR grammar. This class is frequently used to aid
    other classes in processing intermediate structures.
    """
    def __init__(self):
        super().__init__()
        self.functions = []
        self.ids = []
        self.expressions = []
        self.conditions = []
        self.math_expressions = []
        self.builder = Builder()

    @v_args(inline=True)
    def NAME(self, token):
        return ID(token)

    def comp_op(self, items):
        token = items[0]
        if token.type in {"LT", "GT", "EQ", "GTE", "LTE", "NEQ", "NEQ", "IS"}:
            return token.value

    def COND_ANY(self, token):
        return [token.value]

    def condition_list(self, items):
        return items

    def condition(self, items):
        self.conditions.append(items[0])
        return items[0]

    def cond(self, items):
        condition = self.builder.build_condition(items)
        return condition

    def expr(self, items):
        self.expressions.append(items)
        return items[0]

    def term(self, items):
        return items[0]

    def factor(self, items):
        return items[0]

    def atom(self, items):
        return items[0]

    def comparison(self, items):
        comp = self.builder.build_comparison(comparison=items)
        return comp

    def arith_op(self, items):
        token = items[0]
        if token.type in {"PLUS", "MINUS", "DIV", "MOD", "MUL"}:
            return token.value

    def bitwise_op(self, items):
        token = items[0]
        if token.type in {"BAND", "BOR", "BLS", "BRS", "BXOR"}:
            return token.value

    def BNOT(self, token):
        return token.value

    def param_list(self, items):
        return items

    def parameters(self, items):
        return items[0]

    @v_args(inline=True)
    def func(self, name, *args):
        routine = FuncCall(name, list(args[0]))
        self.functions.append(routine)
        return routine

    @v_args(inline=True)
    def args(self, *args):
        return args

    def SIGN(self, token):
        return [token.value]

    @v_args(inline=True)
    def NUMBER(self, token):
        return Number(token)

    @v_args(inline=True)
    def add(self, left, right):
        return Add(left, right)

    @v_args(inline=True)
    def sub(self, left, right):
        return Sub(left, right)

    @v_args(inline=True)
    def mul(self, left, right):
        return Mul(left, right)

    @v_args(inline=True)
    def div(self, left, right):
        return Div(left, right)

    @v_args(inline=True)
    def mod(self, left, right):
        return Div(left, right)

    @v_args(inline=True)
    def bitand(self, left, right):
        return BitwiseAND(left, right)

    @v_args(inline=True)
    def bitor(self, left, right):
        return BitwiseOR(left, right)

    @v_args(inline=True)
    def bitxor(self, left, right):
        return BitwiseXOR(left, right)

    @v_args(inline=True)
    def bitrs(self, left, right):
        return BitwiseRightShift(left, right)

    @v_args(inline=True)
    def bitls(self, left, right):
        return BitwiseLeftShift(left, right)

    @v_args(inline=True)
    def neg(self, expr):
        return Neg(expr)

    @v_args(inline=True)
    def pos(self, expr):
        return Pos(expr)

    @v_args(inline=True)
    def bitnot(self, expr):
        return BitwiseNOT(expr)

    def NOT(self, token):
        return [token.value]

    def ANDOR(self, token):
        return token.value

    def BOOL(self, token):
        return Bool(boolean=token)

    def IS(self, token):
        return token.value

    def return_types(self, items):
        return items

    def NONE(self, token):
        return token.value


class VarParser(Transformer):
    """
    The VarParser class inherits the Lark's Transformer methods to parse NAR Var blocks.
    """
    def __init__(self):
        super().__init__()
        self.vars = []

    @v_args(inline=True)
    def var(self, parameters, type_):
        """
        The var() takes in all the variable IDs in the provided NAR and builds Variable structures for every
        one of them.
        :param parameters: variable IDs (1 or more, and of the same type).
        :param type_: the type of the provided variable.
        :return: Nothing, it builds a list of Variables.
        """
        for parameter in parameters:
            variable = Variable(var_id=parameter, var_type=type_, write_permission=False)
            self.vars.append(Var(variable))

    @v_args(inline=True)
    def param_list(self, *items):
        """
        The param_list() parses all the variable IDs separated by commas, and returns a list of them (Parameter List).
        :param items: comma-separated variable IDs.
        :return: list of variable IDs.
        """
        return items


class ActionParser(Utility):
    """
        The ActionParser class inherits the Lark's Transformer methods to parse NAR Action blocks.
    """
    def __init__(self):
        super().__init__()
        self.actions = []
        self.functions = []
        self.ids = []
        self.expressions = []
        self.conditions = []

    def action_list(self, items):
        """
        The action_list() method returns all the actions defined by the 'action_list' grammar rule .
        :param items: actions.
        :return: actions' list.
        """
        return items

    @v_args(inline=True)
    def action(self, assignment, condition):
        """
        The action() method builds an NAR Action structure by taking in the assignment of the action and the condition
        under which it's performed.
        :param assignment: The assignment statement (e.g. x = y).
        :param condition: the condition statement (e.g. condition ANY).
        :return: Nothing, it adds the new action to the current list of actions.
        """
        if assignment != 'None':
            __action__object = Action(lvalue=assignment[0], rvalue=assignment[1], condition=condition)
            self.actions.append(__action__object)

    @v_args(inline=True)
    def assignment(self, lvalue, rvalue):
        """
        The assignment() method returns a list containing the left and right values of the assignment statement of the action.
        :param lvalue: The left value of the assignment (it must be a variable).
        :param rvalue: The right value of the assignment.
        :return: list containing lvalue and rvalue of the assignment.
        """
        return [lvalue, rvalue]


class ReturnParser(Utility):
    """
        The ReturnParser class inherits the Lark's Transformer methods to parse NAR Return blocks.
    """
    def __init__(self):
        super().__init__()
        self.returns = []

    def return_block(self, items):
        """
            The return_block() method returns the targeted content of 'return_block' grammar rule .
            :param items: 'return_block' raw content.
            :return: 'return_block' targeted content.
        """
        return items[0]

    def return_list(self, items):
        """
            The return_list() method returns all the return statements defined by the 'return_list' grammar rule .
            :param items: returns.
            :return: returns' list.
        """
        return items

    def return_(self, items):
        """
        the return_() method takes in a list of items corresponding to NAR return statements and builds an NAR Return
        structure.
        :param items: Parsed items.
        :return: Nothing, it adds the Return structure to a list.
        """
        if items[0] != 'None':
            ret = items[0][0]
            condition = items[1]
            __return__object = Return(output=ret, condition=condition)
            self.returns.append(__return__object)
            return items

    @staticmethod
    def print_return(__return__: list):
        """
        The print_return() takes in a list of Return structures and return a string version of each element.
        :param __return__: List of Return structures.
        :return: A string version of each Return structure.
        """
        out = ''
        for items in __return__:
            for item in items:
                if isinstance(item, Expr):
                    out += f"{item.print()} condition"
                if isinstance(item, Condition):
                    out += f"{item.reconstruct()}"
                elif isinstance(item, str):
                    out += f"{item}"

                out += " "

        out = out.strip()

        return out


if __name__ == '__main__':

    pass
