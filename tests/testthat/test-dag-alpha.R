test_that("literal binding and shadowing remain distinct under DAG alpha comparison", {
  cases <- list(
    list("forall x. exists x. x = y", "forall x. exists x. x = y", TRUE),
    list("forall x. exists x. x = y", "forall a. exists b. b = y", TRUE),
    list("forall x. exists x. x = y", "forall a. exists b. a = y", FALSE),
    list("forall x. x = y", "forall y. y = y", FALSE),
    list("forall x. exists y. x = y", "forall x. exists y. x = x", FALSE))
  for (case in cases) {
    expect_identical(dag_alpha_equal(arithmetic_dag(parse_formula(case[[1L]])),
                                    arithmetic_dag(parse_formula(case[[2L]]))), case[[3L]])
  }
})

test_that("irrelevant prefix changes preserve denoted syntax", {
  first <- list(schema_version="1.0", nodes=list(
    list(op="zero",name="",args=list()),
    list(op="var",name="x0",args=list()),
    list(op="eq",name="",args=list(1L,1L))),root=2L)
  different <- first
  different$nodes[[1L]] <- list(op="num",name="7",args=list())
  shorter <- list(schema_version="1.0", nodes=list(
    list(op="var",name="x0",args=list()),
    list(op="eq",name="",args=list(0L,0L))),root=1L)
  expect_true(dag_alpha_equal(first,different))
  expect_true(dag_alpha_equal(first,shorter))
  expect_true(dag_alpha_equal(first,first))
})

test_that("identical invalid graphs are still rejected", {
  invalid <- list(schema_version="1.0",nodes=list(
    list(op="succ",name="",args=list(0L))),root=0L)
  expect_error(dag_alpha_equal(invalid,invalid),class="goedel_error")
})
