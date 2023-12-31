include("julia_to_dl_ir.jl")

function expression_to_string(expression::Expression)
    symbol_to_string = Dict(
        plus => "+",
        minus => "-",
        mult => "*",
        Elenchos.div => "/"
    )
    if expression.symbol == symbol
        #TODO: Handle the edge cases, e.g., x_1, x_2, etc.
        return snake_case_to_camel_case("$(expression.left)")
    elseif expression.symbol == Elenchos.real
        return "$(expression.left)"
    elseif expression.symbol in [plus, minus, mult, Elenchos.div]
        return "$(expression_to_string(expression.left)) " * symbol_to_string[expression.symbol] * " $(expression_to_string(expression.right))"
    end
end


function formula_to_string(formula::Formula)
    symbol_to_string = Dict(
        less_or_equal => "<=",
        greater_or_equal => ">=",
        Elenchos.less => "<",
        greater => ">",
        equal => "=",
        not_equal => "!=",
        and => "&",
        or => "|",
        not => "!",
        bool_true => "true",
        bool_false => "false"
    )
    if formula.symbol in [less_or_equal, greater_or_equal, Elenchos.less, greater, equal, not_equal]
        return "$(expression_to_string(formula.first_expressions)) " * symbol_to_string[formula.symbol] * " $(expression_to_string(formula.second_expressions))"
    elseif formula.symbol in [and, or]
        return "$(formula_to_string(formula.first_subformula)) " * symbol_to_string[formula.symbol] * " $(formula_to_string(formula.second_subformula))"
    elseif formula.symbol == not
        return symbol_to_string[formula.symbol] * "($(formula_to_string(formula.first_subformula)))"
    elseif formula.symbol in [bool_true, bool_false]
        return symbol_to_string[formula.symbol]
    end
end


function program_to_string(program::Program)
    symbol_to_string = Dict(
        assign => ":=",
        choice => "∪",
        sequential => ";",
        dl_test => "?"
    )
    if program.symbol == assign
        return "$(expression_to_string(program.expressions[1])) " * symbol_to_string[program.symbol] * " $(expression_to_string(program.expressions[2]))"
    elseif program.symbol == choice
        return "{$(program_to_string(program.first_programs)) " * symbol_to_string[program.symbol] * " $(program_to_string(program.second_programs))}"
    elseif program.symbol == sequential
        return "$(program_to_string(program.first_programs))" * symbol_to_string[program.symbol] * " $(program_to_string(program.second_programs))"
    elseif program.symbol == dl_test
        return symbol_to_string[program.symbol] * "($(formula_to_string(program.formula)))"
    elseif program.symbol == empty
        return ""
    end
end