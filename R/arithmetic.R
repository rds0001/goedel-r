.decimal <- function(x) {
  if (!.scalar_string(x) || !grepl("^(0|[1-9][0-9]*)$", x)) .fail("Expected canonical decimal string")
  if (nchar(x) > 4096L) .fail("Numeral exceeds 4096 digits", "RESOURCE_LIMIT")
  x
}
.dec_add <- function(a, b) {
  aa <- rev(utf8ToInt(a) - 48L); bb <- rev(utf8ToInt(b) - 48L)
  n <- max(length(aa), length(bb)); length(aa) <- n; length(bb) <- n
  aa[is.na(aa)] <- 0L; bb[is.na(bb)] <- 0L; out <- integer(n); carry <- 0L
  for (i in seq_len(n)) { z <- aa[i] + bb[i] + carry; out[i] <- z %% 10L; carry <- z %/% 10L }
  if (carry) out <- c(out, carry)
  .decimal(paste(rev(out), collapse = ""))
}
.dec_mul <- function(a, b) {
  if (a == "0" || b == "0") return("0")
  aa <- rev(utf8ToInt(a) - 48L); bb <- rev(utf8ToInt(b) - 48L)
  if (length(aa) + length(bb) > 4097L) .fail("Arithmetic result too large", "RESOURCE_LIMIT")
  out <- numeric(length(aa) + length(bb))
  for (i in seq_along(aa)) for (j in seq_along(bb)) out[i+j-1L] <- out[i+j-1L] + aa[i]*bb[j]
  for (i in seq_len(length(out)-1L)) { out[i+1L] <- out[i+1L] + out[i] %/% 10; out[i] <- out[i] %% 10 }
  while (length(out)>1L && tail(out,1L)==0) out <- head(out,-1L)
  .decimal(paste(rev(out), collapse=""))
}
.dec_half <- function(x) {
  ds <- utf8ToInt(x)-48L; carry <- 0L
  for (i in seq_along(ds)) { z <- carry*10L+ds[i]; ds[i] <- z %/% 2L; carry <- z %% 2L }
  value <- sub("^0+", "", paste(ds,collapse="")); if (!nzchar(value)) value <- "0"
  list(value=value,remainder=carry)
}
.arithmetic_ok <- function(x) {
  if (x$kind == "const" && x$name != "zero") return(FALSE)
  if (x$kind == "func" && (!x$name %in% c("S","add","mul") || length(x$args) != if (x$name=="S") 1L else 2L)) return(FALSE)
  if (x$kind == "pred") return(FALSE)
  all(vapply(x$args, .arithmetic_ok, logical(1)))
}
#' Arithmetic Language, Exact Numerals and Robinson or Peano Theories
#'
#' Numerals are explicit abbreviations for binary Horner terms in zero, successor
#' and multiplication, never machine doubles. Expansion retains the syntax limits
#' of 1000 nodes and depth 64. Q has seven conventional axioms. PA uses those seven
#' axioms and the full first-order induction schema in the arithmetic signature;
#' Q's predecessor axiom is redundant in this presentation of PA. No theory object
#' certifies consistency. Extra axioms are closed, explicitly trusted formulas.
#' Induction recognition is syntactic modulo bound variable names; an open schema
#' instance is recognized but is not a theory axiom until universally closed.
#' @param value A canonical nonnegative decimal string of at most 4096 digits.
#' @param term A term.
#' @param left,right Arithmetic terms.
#' @param max_nodes Expansion budget, an integer in 1 through 1000.
#' @param body An arithmetic formula.
#' @param variable The induction variable name.
#' @param close Whether to universally close all remaining free parameters.
#' @param formula A formula to recognize or check.
#' @param name Either Q or PA.
#' @param extensions An unnamed list of additional closed arithmetic axioms.
#' @param theory An arithmetic theory descriptor.
#' @return Constructors return syntax expressions; numerical evaluation returns an
#' exact decimal string; descriptors and recognition return lists; axiom membership
#' returns a logical scalar.
#' @examples
#' numeral_value(add(numeral("123"), numeral("456")))
#' expand_numeral(numeral("5"))
#' pa <- arithmetic_theory("PA")
#' f <- induction_axiom(equal(variable("x"), variable("x")), "x")
#' is_axiom(pa, f)
#' @export
numeral <- function(value) .expr("num", .decimal(value))
#' @rdname numeral
#' @export
zero <- function() constant("zero")
#' @rdname numeral
#' @export
successor <- function(term) function_term("S", list(term))
#' @rdname numeral
#' @export
add <- function(left,right) function_term("add",list(left,right))
#' @rdname numeral
#' @export
multiply <- function(left,right) function_term("mul",list(left,right))
#' @rdname numeral
#' @export
numeral_value <- function(term) {
  .require_term(term)
  walk <- function(x) {
    if (x$kind=="num") return(x$name)
    if (x$kind=="const" && x$name=="zero") return("0")
    if (x$kind=="func" && x$name=="S" && length(x$args)==1L) return(.dec_add(walk(x$args[[1L]]),"1"))
    if (x$kind=="func" && x$name %in% c("add","mul") && length(x$args)==2L)
      return(if(x$name=="add") .dec_add(walk(x$args[[1L]]),walk(x$args[[2L]])) else .dec_mul(walk(x$args[[1L]]),walk(x$args[[2L]])))
    .fail("Not a closed arithmetic term")
  }; walk(term)
}
#' @rdname numeral
#' @export
expand_numeral <- function(term,max_nodes=1000L) {
  .validate(term); .int_budget(max_nodes,1000L,"max_nodes")
  n <- 0L
  node <- function(kind,name="",args=list()) {
    n <<- n+1L; if(n>max_nodes) .fail("Numeral expansion budget exceeded","RESOURCE_LIMIT")
    structure(list(args=args,kind=kind,name=name),class="goedel_expr")
  }
  nu <- function(s,depth=1L) {
    if(depth>64L) .fail("Numeral expansion depth exceeded","RESOURCE_LIMIT")
    z <- function() node("const","zero")
    succ <- function(t) node("func","S",list(t))
    if(s=="0") return(z())
    if(s=="1") return(succ(z()))
    h <- .dec_half(s); out <- node("func","mul",list(succ(succ(z())),nu(h$value,depth+2L)))
    if(h$remainder) out <- succ(out)
    out
  }
  walk <- function(x) if(x$kind=="num") nu(x$name) else node(x$kind,x$name,lapply(x$args,walk))
  out <- walk(term); .validate(out); out
}
.int_budget <- function(x,maximum,label="max_steps") {
  if (!is.numeric(x)||is.logical(x)||length(x)!=1L||is.na(x)||!is.finite(x)||x!=floor(x)||x<1||x>maximum) .fail(paste(label,"outside integer budget"))
  invisible(x)
}
#' @rdname numeral
#' @export
arithmetic_language <- function() list(id="goedel-arithmetic-v1",constants=list("zero"),
  functions=list(list(name="S",arity=1L),list(name="add",arity=2L),list(name="mul",arity=2L)),
  relations=list(),equality=TRUE,numerals="binary-horner-v1")
#' @rdname numeral
#' @export
q_axioms <- function() {
  x <- variable("x"); y <- variable("y")
  list(forall("x",negate(equal(successor(x),zero()))),
    forall("x",forall("y",implication(equal(successor(x),successor(y)),equal(x,y)))),
    forall("x",implication(negate(equal(x,zero())),exists_formula("y",equal(x,successor(y))))),
    forall("x",equal(add(x,zero()),x)),
    forall("x",forall("y",equal(add(x,successor(y)),successor(add(x,y))))),
    forall("x",equal(multiply(x,zero()),zero())),
    forall("x",forall("y",equal(multiply(x,successor(y)),add(multiply(x,y),x)))))
}
#' @rdname numeral
#' @export
induction_axiom <- function(body,variable,close=TRUE) {
  .require_formula(body); if(!.name_ok(variable)||!is.logical(close)||length(close)!=1L||is.na(close)) .fail("Invalid induction arguments")
  if(!.arithmetic_ok(body)) .fail("Induction body must use the arithmetic signature")
  base <- substitute_formula(body,variable,zero())
  step <- forall(variable,implication(body,substitute_formula(body,variable,successor(get("variable",mode="function")(variable)))))
  out <- implication(conjunction(base,step),forall(variable,body))
  if(close) for(p in rev(setdiff(free_variables(body),variable))) out <- forall(p,out)
  out
}
#' @rdname numeral
#' @export
recognize_induction <- function(formula) {
  .require_formula(formula); if(!.arithmetic_ok(formula)) .fail("Expected arithmetic signature"); fail <- list(is_instance=FALSE,variable=NULL,body=NULL,parameters=list())
  f <- formula; outer <- character()
  while(f$kind=="forall") { outer <- c(outer,f$name); f <- f$args[[1L]] }
  if(f$kind!="implies"||f$args[[2L]]$kind!="forall") return(fail)
  rhs <- f$args[[2L]]; b <- rhs$args[[1L]]; v <- rhs$name
  if(!.arithmetic_ok(b)) return(fail)
  pars <- setdiff(free_variables(b),v)
  if(length(outer) && (anyDuplicated(outer)||!setequal(outer,pars))) return(fail)
  if(!alpha_equal(f,induction_axiom(b,v,FALSE))) return(fail)
  list(is_instance=TRUE,variable=v,body=b,parameters=as.list(pars))
}
#' @rdname numeral
#' @export
arithmetic_theory <- function(name="PA",extensions=list()) {
  if(!.scalar_string(name)||!name %in% c("Q","PA")) .fail("Theory must be Q or PA")
  .formula_list(extensions,"extensions")
  if(length(extensions)>256L) .fail("Theory extension budget exceeded","RESOURCE_LIMIT")
  if(any(vapply(extensions,function(x) length(free_variables(x))>0L||!.arithmetic_ok(x),logical(1)))) .fail("Extensions must be closed arithmetic formulas")
  if(anyDuplicated(vapply(extensions,function(x) .wire_json(normalize(x)),""))) .fail("Duplicate extension")
  list(id=name,version="1.0",signature=arithmetic_language(),logic="CLASSICAL_FOL_EQUALITY",axioms=q_axioms(),
    schemas=if(name=="PA") list("PA_INDUCTION") else list(),presentation=list(kind="DECIDABLE",id=paste0("goedel-",name,"-v1")),
    extensions=extensions,consistency_status="NOT_ESTABLISHED")
}
.validate_theory <- function(theory) {
  if(!is.list(theory)||is.null(theory[["id"]])||is.null(theory[["extensions"]])) .fail("Invalid theory descriptor")
  expected <- arithmetic_theory(theory[["id"]],theory[["extensions"]])
  canon <- function(x) { if(inherits(x,"goedel_expr")) x <- unclass(x); if(is.list(x)) {x <- lapply(x,canon); if(!is.null(names(x))) x <- x[order(names(x),method="radix")]};x }
  if(!identical(jsonlite::toJSON(canon(theory),auto_unbox=TRUE),jsonlite::toJSON(canon(expected),auto_unbox=TRUE))) .fail("Tampered theory descriptor")
  invisible(TRUE)
}
#' @rdname numeral
#' @export
is_axiom <- function(theory,formula) {
  .validate_theory(theory); .require_formula(formula)
  if(!.arithmetic_ok(formula)) .fail("Expected arithmetic signature")
  if(length(free_variables(formula))) return(FALSE)
  if(any(vapply(c(theory$axioms,theory$extensions),function(x) alpha_equal(x,formula),logical(1)))) return(TRUE)
  theory$id=="PA" && recognize_induction(formula)$is_instance
}
