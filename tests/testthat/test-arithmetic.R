test_that("exact decimal arithmetic agrees with independent small integer oracle", {
  for(a in c(0L,1L,2L,7L,99L,1234L))for(b in c(0L,1L,3L,25L,876L)) {
    expect_identical(numeral_value(add(numeral(as.character(a)),numeral(as.character(b)))),as.character(a+b))
    expect_identical(numeral_value(multiply(numeral(as.character(a)),numeral(as.character(b)))),as.character(a*b))
  }
  expect_identical(numeral_value(successor(numeral("999999999999999999999999"))),"1000000000000000000000000")
  expect_identical(numeral_value(multiply(numeral("123456789"),numeral("987654321"))),"121932631112635269")
  for(n in 0:30)expect_identical(numeral_value(expand_numeral(numeral(as.character(n)))),as.character(n))
  expect_error(numeral("01"),class="goedel_error")
  expect_error(numeral(1),class="goedel_error")
  expect_error(numeral_value(variable("x")),class="goedel_error")
  expect_error(expand_numeral(numeral("5"),max_nodes=3),class="goedel_error")
  expect_identical(serialize_record(decode(encode(numeral("123")))) ,serialize_record(numeral("123")))
})
test_that("Q axioms and PA schema membership have explicit signature and closure", {
  q<-arithmetic_theory("Q");pa<-arithmetic_theory("PA")
  expect_length(q_axioms(),7L)
  for(f in q_axioms()){expect_true(is_axiom(q,f));expect_length(free_variables(f),0L)}
  expect_identical(format_formula(q_axioms()[[1L]]),"(forall x. !((S(x) = @zero)))")
  x<-variable("x");y<-variable("y");body<-equal(add(x,y),add(y,x))
  ax<-induction_axiom(body,"x")
  expect_true(is_axiom(pa,ax));expect_false(is_axiom(q,ax))
  expect_true(recognize_induction(ax)$is_instance)
  expect_identical(recognize_induction(ax)$parameters,list("y"))
  open<-induction_axiom(body,"x",close=FALSE)
  expect_true(recognize_induction(open)$is_instance);expect_false(is_axiom(pa,open))
  bad<-ax;bad$args[[1L]]$args[[1L]]$args[[1L]]<-bottom()
  expect_false(is_axiom(pa,bad))
  expect_error(induction_axiom(predicate("P",list(x)),"x"),class="goedel_error")
  badtheory<-pa;badtheory$consistency_status<-"ESTABLISHED"
  expect_error(is_axiom(badtheory,ax),class="goedel_error")
  expect_error(arithmetic_theory("Q",list(equal(x,x))),class="goedel_error")
})
test_that("formula parser preserves syntax and precedence without evaluating text", {
  strings<-c("forall x. exists y. x + 0 = y * 1", "A -> B -> C", "!(A & B) | C", "(x+y)=z", "false()", "forall(x)", "@zero = 0")
  for(s in strings){f<-parse_formula(s);expect_identical(serialize_record(parse_formula(format_formula(f))),serialize_record(f))}
  f<-parse_formula("A -> B -> C");expect_identical(f$args[[2L]]$kind,"implies")
  expect_identical(parse_formula("x + y * z = x")$args[[1L]]$args[[2L]]$name,"mul")
  for(s in c("x=", "A;system(1)", "forall x A", "A && B", "01=1", ""))expect_error(parse_formula(s),class="goedel_error")
})
