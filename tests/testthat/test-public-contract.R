test_that("the public arithmetic signature has the fixed mathematical arities", {
  expect_identical(arithmetic_language(), list(
    id="goedel-arithmetic-v1", constants=list("zero"),
    functions=list(list(name="S",arity=1L),list(name="add",arity=2L),
                   list(name="mul",arity=2L)), relations=list(), equality=TRUE,
    numerals="binary-horner-v1"))
})

test_that("public DAG alpha comparison preserves free versus bound variables", {
  original <- arithmetic_dag(parse_formula("forall x. x = y"))
  renamed <- arithmetic_dag(parse_formula("forall z. z = y"))
  captured <- arithmetic_dag(parse_formula("forall y. y = y"))
  expect_true(dag_alpha_equal(original,renamed))
  expect_false(dag_alpha_equal(original,captured))
  literal <- list(schema_version="1.0",nodes=list(
    list(op="var",name="x0",args=list()),
    list(op="eq",name="",args=list(0L,0L))),root=1L)
  expect_identical(serialize_arithmetic_dag(literal),
    '{"nodes":[{"args":[],"name":"x0","op":"var"},{"args":[0,0],"name":"","op":"eq"}],"root":1,"schema_version":"1.0"}')
})

test_that("modal Boolean constructors agree with a literal truth table", {
  p <- modal_atom("p"); q <- modal_atom("q")
  formulas <- list(modal_conjunction(p,q),modal_disjunction(p,q),modal_negate(p))
  # Rows FF, FT, TF, TT; columns conjunction, disjunction, negation of p.
  expected <- list(c(FALSE,FALSE,TRUE),c(FALSE,TRUE,TRUE),
                   c(FALSE,TRUE,FALSE),c(TRUE,TRUE,FALSE))
  valuations <- list(c(FALSE,FALSE),c(FALSE,TRUE),c(TRUE,FALSE),c(TRUE,TRUE))
  for(i in seq_along(valuations)) {
    values <- valuations[[i]]
    model <- kripke_model(list("w"),list(),list(
      p=if(values[[1L]])list("w") else list(),
      q=if(values[[2L]])list("w") else list()))
    for(j in seq_along(formulas)) {
      expect_identical(evaluate_modal(formulas[[j]],model,"w")$status,
        if(expected[[i]][[j]])"ESTABLISHED" else "REFUTED")
    }
  }
})

test_that("numbered closed substitution rejects bounded syntax outside its profile", {
  nodes <- list(list(op="var",name="x0",args=list()),
                list(op="num",name="2",args=list()),
                list(op="eq",name="",args=list(0L,0L)))
  for(op in c("bforall","bexists")) {
    dag <- list(schema_version="1.0",nodes=c(nodes,
      list(list(op=op,name="x0",args=list(1L,2L)))),root=3L)
    expect_identical(validate_arithmetic_dag(dag,TRUE)$root_sort,"formula")
    expect_error(dag_substitute_numeral(dag,"x0","1"),class="goedel_error")
  }
  less <- list(schema_version="1.0",nodes=c(nodes[1:2],
    list(list(op="lt",name="",args=list(0L,1L)))),root=2L)
  expect_identical(validate_arithmetic_dag(less,TRUE)$root_sort,"formula")
  expect_error(dag_substitute_numeral(less,"x0","1"),class="goedel_error")
})
