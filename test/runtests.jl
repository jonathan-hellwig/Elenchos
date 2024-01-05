import Test
using MacroTools, Elenchos


# """
# function example(x::Elenchos.Real)
#     @assume 0 <= x <= 1
#     if x <= 0.5
#         x = 0.0
#     else
#         x = 1.0
#     end
#     @assert 0 <= x <= 1
# end

# ArchiveEntry "example.kyx"
#     ProgramVariables
#         Elenchos.Real x;
#     End.
#     Problem
#         0 <= x & x <= 1 -> [{?x<=0.5; x:=0.0; ++ x:=1.0; }] 0 <= x & x <= 1
#     End.
# End.
# """




# program = Base.remove_linenums!(quote
#     max_value = y
# end
# )

# # This does not work because the whole program is wrapped into a symbol block
# # Each branch of the if statement is also a symbol block
# # Therefore, in the end there there are two empty programs
# # This could be resolved by removing the empty programs after each symbol block and instead
# # Adding the empty program to the end of each assignment
# program = Base.remove_linenums!(quote
#     if x >= y
#         max_value = x
#     else
#         max_value = y
#     end
# end
# )

# @Test.test program_to_kyx(program) == Choice(
#     Sequential(
#             DlTest(GreaterOrEqual(DlSymbol(:x), DlSymbol(:y))),
#             Sequential(
#                 Assignment(DlSymbol(:max_value), DlSymbol(:x)),
#                 Empty()
#             )
#         ),
#     Sequential(
#         DlTest(Not(GreaterOrEqual(DlSymbol(:x), DlSymbol(:y)))),
#         Sequential(
#             Assignment(DlSymbol(:max_value), DlSymbol(:y)),
#             Empty()
#         )
#     )
# )

include("test_dl_ir.jl")
include("test_macro.jl")
include("test_dl_ir_to_string.jl")