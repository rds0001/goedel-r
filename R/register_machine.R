.ascii_json <- function(x) {
  text<-.proof_json(x);ints<-utf8ToInt(text);if(all(ints<128L))return(text)
  paste(vapply(ints,function(v){if(v<128L)intToUtf8(v) else if(v<=65535L)sprintf("\\u%04x",v) else {u<-v-65536L;paste0(sprintf("\\u%04x",55296L+u%/%1024L),sprintf("\\u%04x",56320L+u%%1024L))}},""),collapse="")
}
.register_hash <- function(program) digest::digest(.ascii_json(program),algo="sha256",serialize=FALSE)
.register_fields <- list(CONST=c("dst","value","next"),COPY=c("dst","src","next"),ADD=c("dst","left","right","next"),MUL=c("dst","left","right","next"),SUB=c("dst","left","right","next"),DIVMOD=c("quotient","remainder","numerator","denominator","next"),JEQ=c("left","right","then","else"),JLT=c("left","right","then","else"),JUMP="next",HALT=character())
.register_integer <- function(x,lower,upper) is.numeric(x)&&!is.logical(x)&&length(x)==1L&&!is.na(x)&&is.finite(x)&&x==floor(x)&&x>=lower&&x<=upper
.register_validate <- function(program) {
  if(!.fields(program,c("id","version","register_count","inputs","output","entry","instructions"))||!.scalar_string(program$id)||!nzchar(program$id)||!.scalar_string(program$version)||!nzchar(program$version)) .fail("Invalid register program envelope")
  count<-program$register_count;if(!.register_integer(count,1L,4096L)) .fail("Invalid register count")
  .array(program$instructions,"instructions");n<-length(program$instructions)
  if(n<1L||n>100000L) .fail("Invalid instruction count")
  .array(program$inputs,"input registers")
  if(anyDuplicated(unlist(program$inputs))||!all(vapply(program$inputs,.register_integer,logical(1),lower=0L,upper=count-1L))) .fail("Invalid input register layout")
  if(!.register_integer(program$output,0L,count-1L)||!.register_integer(program$entry,0L,n-1L)) .fail("Invalid output or entry index")
  halts<-FALSE
  for(ins in program$instructions) {
    if(!is.list(ins)||!.scalar_string(ins[["op"]])||!ins[["op"]] %in% names(.register_fields)||!.fields(ins,c("op",.register_fields[[ins[["op"]]]]))) .fail("Invalid register instruction")
    op<-ins$op
    for(field in setdiff(names(ins),c("op","value")))if(!.register_integer(ins[[field]],0L,if(field %in% c("next","then","else"))n-1L else count-1L)) .fail("Invalid instruction operand")
    if(op=="CONST") .decimal(ins$value)
    if(op=="DIVMOD"&&ins$quotient==ins$remainder) .fail("DIVMOD destinations must differ")
    if(op=="HALT")halts<-TRUE
  }
  if(!halts) .fail("Program requires an explicit HALT")
  invisible(TRUE)
}
.register_inputs <- function(program,inputs) {
  if(is.character(inputs))inputs<-as.list(inputs);.array(inputs,"inputs")
  if(length(inputs)!=length(program$inputs)) .fail("Input arity mismatch")
  values<-lapply(inputs,.big_nat,max_digits=5000000L)
  for(v in values)if(gmp::sizeinbase(v,2L)>16000000L) .fail("Register bit budget exceeded","RESOURCE_LIMIT")
  values
}
.register_initial <- function(program,values) {
  registers<-rep(list(gmp::as.bigz(0)),program$register_count)
  for(i in seq_along(values))registers[[program$inputs[[i]]+1L]]<-values[[i]]
  list(pc=as.integer(program$entry),registers=registers)
}
.register_wire <- function(state) list(pc=state$pc,registers=lapply(state$registers,as.character))
.register_step <- function(program,state,constants=NULL) {
  ins<-program$instructions[[state$pc+1L]];r<-state$registers;op<-ins$op
  read<-function(name)r[[ins[[name]]+1L]]
  if(op=="HALT")return(state)
  if(op %in% c("CONST","COPY","ADD","MUL","SUB")) {
    value<-switch(op,CONST=if(is.null(constants))gmp::as.bigz(ins$value) else constants[[state$pc+1L]],COPY=read("src"),ADD=read("left")+read("right"),MUL=read("left")*read("right"),SUB={a<-read("left");b<-read("right");if(a<b)gmp::as.bigz(0) else a-b})
    r[[ins$dst+1L]]<-value
  } else if(op=="DIVMOD") {
    a<-read("numerator");b<-read("denominator");q<-if(b==0L)gmp::as.bigz(0) else a%/%b;rem<-if(b==0L)a else a%%b
    r[[ins$quotient+1L]]<-q;r[[ins$remainder+1L]]<-rem
  }
  next_pc<-if(op %in% c("JEQ","JLT")) {condition<-if(op=="JEQ")read("left")==read("right") else read("left")<read("right");if(condition)ins[["then"]] else ins[["else"]]} else ins[["next"]]
  # Initially every register is bounded. COPY/SUB/DIVMOD cannot increase the
  # largest operand; CONST is bounded by the validated 4096-digit source limit.
  # Only ADD and MUL need a new size check after a transition.
  if(op %in% c("ADD","MUL")&&gmp::sizeinbase(value,2L)>16000000L) .fail("Register bit budget exceeded","RESOURCE_LIMIT")
  list(pc=as.integer(next_pc),registers=r)
}
.register_limit <- "This is a finite computation of an explicit register program; runtime exhaustion is not a mathematical negative result or a proof of representability."
#' Execute and Independently Check Explicit Register Computations
#'
#' The machine has natural-number registers and CONST, COPY, ADD, MUL, saturating
#' SUB, total DIVMOD, JEQ, JLT, JUMP and HALT instructions. Indices are zero-based.
#' Division by zero yields quotient zero and unchanged numerator as remainder.
#' Each instruction reads all operands before writing, including aliased destinations.
#' The step budget returns UNKNOWN when exhausted. Hard resource limits are
#' 16000000 bits per register and 10000 recorded trace states. These limits do not
#' alter the unbounded mathematical machine relation. Trace replay checks each
#' submitted transition independently of the execution loop.
#' @param program A versioned explicit register program descriptor.
#' @param inputs Natural decimal strings in the program's declared input order.
#' @param max_steps Maximum non-HALT transitions, from 1 through 1000000.
#' @param trace For execution, whether to record states; for replay, an explicit
#' nonempty list of states with pc and register strings.
#' @return A finite-computation result with final registers, status and optional trace.
#' @export
run_register_program <- function(program,inputs,max_steps=100000L,trace=FALSE) {
  .register_validate(program);values<-.register_inputs(program,inputs);.int_budget(max_steps,1000000L)
  if(!is.logical(trace)||length(trace)!=1L||is.na(trace)) .fail("trace must be boolean")
  constants<-lapply(program$instructions,function(ins)if(ins$op=="CONST")gmp::as.bigz(ins$value) else NULL)
  state<-.register_initial(program,values);used<-0L;history<-if(trace)list(.register_wire(state)) else NULL
  repeat {
    halted<-program$instructions[[state$pc+1L]]$op=="HALT"
    if(halted||used>=max_steps)break
    if(trace&&length(history)>=10000L) .fail("Register trace budget exceeded","RESOURCE_LIMIT")
    state<-.register_step(program,state,constants);used<-used+1L
    if(trace)history[[length(history)+1L]]<-.register_wire(state)
  }
  .result(if(halted)"ESTABLISHED" else "UNKNOWN","FINITE_COMPUTATION","register_program_execution",limitations=.register_limit,witness=history,
    details=list(steps_used=used,halted=halted,output=if(halted)as.character(state$registers[[program$output+1L]]) else NULL,pc=state$pc,registers=lapply(state$registers,as.character)),
    context=list(program_sha256=.register_hash(program),machine_id="goedel-arithmetic-register-v1"))
}
#' @rdname run_register_program
#' @export
check_register_trace <- function(program,inputs,trace) {
  states<-trace
  .register_validate(program);values<-.register_inputs(program,inputs);.array(states,"states")
  if(!length(states)) .fail("Trace requires its initial state")
  if(length(states)>10000L) .fail("Register trace budget exceeded","RESOURCE_LIMIT")
  parsed<-lapply(states,function(s) {
    if(!.fields(s,c("pc","registers"))||!.register_integer(s$pc,0L,length(program$instructions)-1L)) .fail("Invalid trace state")
    .array(s$registers,"registers");if(length(s$registers)!=program$register_count) .fail("Trace register arity mismatch")
    r<-lapply(s$registers,.big_nat,max_digits=5000000L)
    for(v in r)if(gmp::sizeinbase(v,2L)>16000000L) .fail("Register bit budget exceeded","RESOURCE_LIMIT")
    list(pc=as.integer(s$pc),registers=r)
  })
  checked<-0L
  finish<-function(valid,invalid_step=NULL,reason="VALID") {
    last<-tail(parsed,1L)[[1L]];halted<-valid&&program$instructions[[last$pc+1L]]$op=="HALT"
    .result(if(valid)"ESTABLISHED" else "REFUTED","FINITE_COMPUTATION","validity_of_submitted_register_trace",limitations=.register_limit,witness=if(valid)states else NULL,
      details=list(invalid_step=invalid_step,reason=reason,steps_checked=checked,halted=halted,output=if(halted)as.character(last$registers[[program$output+1L]]) else NULL),
      context=list(program_sha256=.register_hash(program),machine_id="goedel-arithmetic-register-v1"))
  }
  initial<-.register_initial(program,values)
  if(parsed[[1L]]$pc!=initial$pc||any(vapply(seq_along(initial$registers),function(i)parsed[[1L]]$registers[[i]]!=initial$registers[[i]],logical(1))))return(finish(FALSE,1L,"INITIAL_STATE_MISMATCH"))
  if(length(parsed)>1L)for(i in seq.int(2L,length(parsed))) {
    before<-parsed[[i-1L]];after<-parsed[[i]];ins<-program$instructions[[before$pc+1L]];op<-ins$op
    a<-before$registers;b<-after$registers;read<-function(name)a[[ins[[name]]+1L]];written<-integer();valid<-TRUE
    if(op=="HALT")valid<-FALSE
    else if(op %in% c("CONST","COPY","ADD","MUL","SUB")) {
      dst<-ins$dst+1L;written<-dst
      if(op=="CONST")valid<-b[[dst]]==gmp::as.bigz(ins$value)
      if(op=="COPY")valid<-b[[dst]]==read("src")
      if(op=="ADD")valid<-b[[dst]]==read("left")+read("right")
      if(op=="MUL")valid<-b[[dst]]==read("left")*read("right")
      if(op=="SUB"){left<-read("left");right<-read("right");valid<-if(left<right)b[[dst]]==0L else b[[dst]]+right==left}
    } else if(op=="DIVMOD") {
      q<-ins$quotient+1L;r<-ins$remainder+1L;written<-c(q,r);numerator<-read("numerator");denominator<-read("denominator")
      valid<-if(denominator==0L)b[[q]]==0L&&b[[r]]==numerator else b[[r]]<denominator&&denominator*b[[q]]+b[[r]]==numerator
    }
    if(valid&&length(setdiff(seq_along(a),written)))valid<-all(vapply(setdiff(seq_along(a),written),function(j)a[[j]]==b[[j]],logical(1)))
    if(valid) {
      if(op %in% c("JEQ","JLT")){condition<-if(op=="JEQ")read("left")==read("right") else read("left")<read("right");target<-if(condition)ins[["then"]] else ins[["else"]]} else target<-ins[["next"]]
      valid<-after$pc==target
    }
    if(!valid)return(finish(FALSE,i,"TRANSITION_MISMATCH"))
    checked<-checked+1L
  }
  finish(TRUE)
}
