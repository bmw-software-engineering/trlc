import cvc5

solver = cvc5.Solver()
solver.setLogic("QF_NRA")
solver.setOption("produce-models", "true")

x = solver.mkConst(solver.getRealSort(), "x")

solver.assertFormula(
    solver.mkTerm(cvc5.Kind.EQUAL,
                  solver.mkTerm(cvc5.Kind.MULT, x, x),
                  solver.mkReal(30)))

result = solver.checkSat()
value = solver.getValue(x)

print(result)
print(value.getKind())
print(value)
