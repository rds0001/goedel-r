finite_ring <- function(n=3L) {
  d<-as.character(seq_len(n)-1L)
  fn<-function(name,arity,fun) {
    if(arity==1L)rows<-lapply(d,function(x)list(args=list(x),value=as.character(fun(as.integer(x))%%n)))
    else rows<-unlist(lapply(d,function(x)lapply(d,function(y)list(args=list(x,y),value=as.character(fun(as.integer(x),as.integer(y))%%n)))),recursive=FALSE)
    list(name=name,arity=arity,table=rows)
  }
  finite_structure(d,list(zero="0"),list(fn("S",1L,function(x)x+1L),fn("add",2L,function(x,y)x+y),fn("mul",2L,function(x,y)x*y)))
}
test_that("finite exact interpretation uses full tables and explicit assignment", {
  m<-finite_ring();x<-variable("x");y<-variable("y")
  for(n in 0:25)expect_identical(evaluate_term(numeral(as.character(n)),m)$details$value,as.character(n%%3L))
  expect_identical(evaluate_term(numeral("0"),m)$details$steps_used,2L)
  expect_identical(evaluate_term(numeral("1"),m)$details$steps_used,3L)
  expect_identical(evaluate_formula(forall("x",equal(add(x,zero()),x)),m)$status,"ESTABLISHED")
  r<-evaluate_formula(forall("x",negate(equal(successor(x),zero()))),m)
  expect_identical(r$status,"REFUTED");expect_identical(r$witness$assignment,setNames(list(),character()))
  expect_identical(finite_model_check(list(equal(add(x,y),add(y,x))),m)$status,"ESTABLISHED")
  r<-finite_model_check(q_axioms(),m);expect_identical(r$witness$formula_index,1L)
  expect_identical(r$details$checked_formulas,1L)
  expect_error(evaluate_formula(equal(x,x),m),class="goedel_error")
  expect_error(evaluate_formula(disjunction(negate(bottom()),predicate("Unknown")),m),class="goedel_error")
  expect_error(evaluate_formula(forall("x",equal(x,x)),m,max_steps=1),class="goedel_error")
  bad<-m;bad$functions[[1L]]$table<-list();expect_error(evaluate_term(zero(),bad),class="goedel_error")
})
test_that("numeral abbreviations retain Horner meaning in nonstandard structures", {
  m<-finite_ring(2L)
  # Replace multiplication with the first projection. Then 2 denotes S(S(0)) * S(0), hence zero.
  rec<-which(vapply(m$functions,function(f)f$name=="mul",logical(1)))
  for(i in seq_along(m$functions[[rec]]$table))m$functions[[rec]]$table[[i]]$value<-m$functions[[rec]]$table[[i]]$args[[1L]]
  for(n in 0:12)expect_identical(evaluate_term(numeral(as.character(n)),m)$details$value,evaluate_term(expand_numeral(numeral(as.character(n))),m)$details$value)
})
test_that("finite structure rejects malformed and incomplete relations", {
  rel<-list(name="P",arity=1L,table=list(list(args=list("a"),value=TRUE),list(args=list("b"),value=FALSE)))
  m<-finite_structure(c("a","b"),relations=list(rel))
  r<-evaluate_formula(exists_formula("x",predicate("P",list(variable("x")))),m)
  expect_identical(r$status,"ESTABLISHED");expect_identical(r$witness$assignment,setNames(list(),character()))
  expect_error(finite_structure(c("a","a")),class="goedel_error")
  rel$table[[2L]]$args<-list("a");expect_error(finite_structure(c("a","b"),relations=list(rel)),class="goedel_error")
})

test_that("finite counterexamples replay when quantifiers shadow free names", {
  rel<-list(name="P",arity=1L,table=list(list(args=list("a"),value=TRUE),list(args=list("b"),value=FALSE)))
  model<-finite_structure(c("a","b"),relations=list(rel))
  atom<-predicate("P",list(variable("x")))
  formula<-implication(atom,forall("x",atom))
  result<-finite_model_check(list(formula),model)
  expect_identical(result$status,"REFUTED")
  expect_identical(result$witness$assignment,list(x="a"))
  replay<-evaluate_formula(formula,model,result$witness$assignment)
  expect_identical(replay$status,"REFUTED")
  expect_identical(replay$witness$assignment,list(x="a"))
  expect_identical(evaluate_formula(formula,model,list(x="b"))$status,"ESTABLISHED")
})
