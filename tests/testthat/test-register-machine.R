register_program <- function(instructions,register_count=4L,inputs=list(0L,1L),output=2L)list(id="test-machine",version="1.0",register_count=register_count,inputs=inputs,output=output,entry=0L,instructions=instructions)
test_that("native execution and separate trace constraints agree with arithmetic oracle", {
  p<-register_program(list(list(op="ADD",dst=2L,left=0L,right=1L,`next`=1L),list(op="MUL",dst=2L,left=2L,right=0L,`next`=2L),list(op="DIVMOD",quotient=2L,remainder=1L,numerator=2L,denominator=1L,`next`=3L),list(op="HALT")))
  r<-run_register_program(p,list("10","3"),trace=TRUE)
  expect_identical(r$status,"ESTABLISHED");expect_identical(r$details$output,"43")
  expect_identical(r$details$registers,list("10","1","43","0"))
  expect_identical(r$details$steps_used,3L);expect_length(r$witness,4L)
  expect_identical(check_register_trace(p,list("10","3"),r$witness)$status,"ESTABLISHED")
  mutated<-r$witness;mutated[[4L]]$registers[[1L]]<-"11"
  expect_identical(check_register_trace(p,list("10","3"),mutated)$status,"REFUTED")
  mutated<-r$witness;mutated[[4L]]$registers[[3L]]<-"42"
  expect_identical(check_register_trace(p,list("10","3"),mutated)$status,"REFUTED")
  mutated<-r$witness;mutated[[1L]]$registers[[1L]]<-"9"
  expect_identical(check_register_trace(p,list("10","3"),mutated)$details$reason,"INITIAL_STATE_MISMATCH")
  # Total division by zero gives q=0, r=the complete pre-state numerator.
  r<-run_register_program(p,list("10","0"),trace=TRUE)
  expect_identical(r$details$registers,list("10","100","0","0"))
  expect_identical(check_register_trace(p,list("10","0"),r$witness)$status,"ESTABLISHED")
})
test_that("branching saturating subtraction and step exhaustion remain explicit", {
  p<-register_program(list(list(op="SUB",dst=2L,left=0L,right=1L,`next`=1L),list(op="JLT",left=0L,right=1L,then=3L,`else`=2L),list(op="COPY",dst=3L,src=2L,`next`=4L),list(op="CONST",dst=3L,value="7",`next`=4L),list(op="JEQ",left=2L,right=3L,then=5L,`else`=5L),list(op="HALT")),output=3L)
  for(case in list(list(inputs=list("1","3"),output="7"),list(inputs=list("9","3"),output="6"))) {
    r<-run_register_program(p,case$inputs,trace=TRUE);expect_identical(r$details$output,case$output)
    expect_identical(check_register_trace(p,case$inputs,r$witness)$status,"ESTABLISHED")
  }
  loop<-register_program(list(list(op="JUMP",`next`=0L),list(op="HALT")))
  r<-run_register_program(loop,list("0","0"),max_steps=3L,trace=TRUE)
  expect_identical(r$status,"UNKNOWN");expect_false(r$details$halted);expect_null(r$details$output)
  expect_identical(check_register_trace(loop,list("0","0"),r$witness)$status,"ESTABLISHED")
  expect_error(run_register_program(p,list("0")),class="goedel_error")
  p$instructions[[1L]]$dst<-10L;expect_error(run_register_program(p,list("0","0")),class="goedel_error")
})
