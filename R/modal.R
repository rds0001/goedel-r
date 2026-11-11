.modal_validate <- function(expr) {
  count<-0L;arities<-c(atom=0L,bottom=0L,not=1L,box=1L,diamond=1L,and=2L,or=2L,implies=2L)
  walk<-function(x,depth=1L) {
    count<<-count+1L;if(count>1000L||depth>64L) .fail("Modal syntax budget exceeded","RESOURCE_LIMIT")
    if(!.fields(x,c("args","kind","name"))||!.scalar_string(x$kind)||!x$kind %in% names(arities)||!.scalar_string(x$name)) .fail("Invalid modal node")
    .array(x$args,"modal args");if(length(x$args)!=arities[[x$kind]]) .fail("Modal arity mismatch")
    if(if(x$kind=="atom")!.name_ok(x$name) else x$name!="") .fail("Invalid modal name")
    for(a in x$args)walk(a,depth+1L)
  };walk(expr)
  if(nchar(.wire_json(expr),type="bytes")>65536L) .fail("Modal syntax byte budget exceeded","RESOURCE_LIMIT")
  invisible(TRUE)
}
.modal <- function(kind,name="",args=list()) {x<-structure(list(args=args,kind=kind,name=name),class="goedel_modal");.modal_validate(x);x}
#' Modal Syntax and Exact Finite Kripke Semantics
#'
#' Modal syntax is distinct from first-order syntax. Models give at most 16 worlds,
#' explicit accessibility edges and complete truth sets for each used atom.
#' Evaluation is exact in this model. Frame validation enumerates every valuation
#' of the formula's atoms, returning the first countermodel or finite validity.
#' Enumeration uses sorted atoms and worlds, with the last bit varying fastest.
#' The full valuation space must fit the declared bound before search starts.
#' Frame properties are finite graph properties. None of these results establish
#' arithmetic provability, an arithmetical interpretation, or general GL completeness.
#' @param name An ASCII atom name.
#' @param formula A modal expression.
#' @param left,right Modal expressions.
#' @param worlds A character vector or list of unique domain labels.
#' @param edges A list of ordered pairs of world labels.
#' @param valuation A named list mapping atoms to lists of worlds where they hold.
#' @param model A Kripke model descriptor.
#' @param world The world at which to evaluate.
#' @param max_steps Evaluation budget from 1 through 1000000.
#' @param max_valuations Complete enumeration budget from 1 through 65536.
#' @return Constructors return modal syntax. Models and frame checks return lists;
#' evaluations return finite-exact results and optional countermodels.
#' @examples
#' p <- modal_atom("p")
#' model <- kripke_model(c("a","b"), list(list("a","b")), list(p=list("b")))
#' evaluate_modal(modal_box(p), model, "a")$status
#' frame_check(model)
#' validate_modal_frame(modal_implication(modal_box(p),p), list("a"), list())$status
#' @export
modal_atom <- function(name) .modal("atom",name)
#' @rdname modal_atom
#' @export
modal_bottom <- function() .modal("bottom")
#' @rdname modal_atom
#' @export
modal_negate <- function(formula) .modal("not",args=list(formula))
#' @rdname modal_atom
#' @export
modal_conjunction <- function(left,right) .modal("and",args=list(left,right))
#' @rdname modal_atom
#' @export
modal_disjunction <- function(left,right) .modal("or",args=list(left,right))
#' @rdname modal_atom
#' @export
modal_implication <- function(left,right) .modal("implies",args=list(left,right))
#' @rdname modal_atom
#' @export
modal_box <- function(formula) .modal("box",args=list(formula))
#' @rdname modal_atom
#' @export
modal_diamond <- function(formula) .modal("diamond",args=list(formula))
#' @rdname modal_atom
#' @export
kripke_model <- function(worlds,edges,valuation=.empty_object()) {
  worlds<-.labels(worlds);.array(edges,"edges");keys<-character();pairs<-list()
  for(e in edges) {
    if(is.character(e))e<-as.list(e)
    .array(e,"edge");if(length(e)!=2L||!all(vapply(e,function(v).scalar_string(v)&&v %in% unlist(worlds),logical(1)))) .fail("Invalid accessibility edge")
    key<-paste(unlist(e),collapse="|");if(key %in% keys) .fail("Duplicate accessibility edge")
    keys<-c(keys,key);pairs[[length(pairs)+1L]]<-e
  }
  valuation<-.object(valuation,"valuation")
  for(n in names(valuation)) {
    if(!.name_ok(n)) .fail("Invalid modal atom name")
    vs<-valuation[[n]];if(is.character(vs))vs<-as.list(vs);.array(vs,"true worlds")
    if(!all(vapply(vs,function(v).scalar_string(v)&&v %in% unlist(worlds),logical(1)))||anyDuplicated(unlist(vs))) .fail("Invalid modal valuation")
    valuation[[n]]<-as.list(.sorted(unlist(vs)))
  }
  list(schema_version="1.0",worlds=worlds,edges=pairs[order(keys,method="radix")],valuation=valuation)
}
.kripke <- function(model) {
  if(!.fields(model,c("schema_version","worlds","edges","valuation"))||!identical(model$schema_version,"1.0")) .fail("Unknown Kripke model schema")
  kripke_model(model$worlds,model$edges,model$valuation)
}
#' @rdname modal_atom
#' @export
frame_check <- function(model) {
  m<-.kripke(model);ws<-unlist(m$worlds);n<-length(ws);adj<-matrix(FALSE,n,n)
  for(e in m$edges)adj[match(e[[1L]],ws),match(e[[2L]],ws)]<-TRUE
  reach<-adj
  for(k in seq_len(n))for(i in seq_len(n))for(j in seq_len(n))reach[i,j]<-reach[i,j]||(reach[i,k]&&reach[k,j])
  transitive<-TRUE
  for(i in seq_len(n))for(j in seq_len(n))for(k in seq_len(n))if(adj[i,j]&&adj[j,k]&&!adj[i,k])transitive<-FALSE
  list(reflexive=all(diag(adj)),irreflexive=!any(diag(adj)),transitive=transitive,acyclic=!any(diag(reach)))
}
.modal_atoms <- function(x) .sorted(c(if(x$kind=="atom")x$name else character(),unlist(lapply(x$args,.modal_atoms),use.names=FALSE)))
.modal_limit <- "This result concerns the specified finite Kripke model or frame, not arithmetic provability or general GL completeness."
.modal_evaluator <- function(max_steps) {
  .int_budget(max_steps,1000000L);state<-new.env(parent=emptyenv());state$used<-0L
  truth<-function(x,m,w) {
    state$used<-state$used+1L;if(state$used>max_steps) .fail("Finite evaluation budget exhausted","RESOURCE_LIMIT")
    k<-x$kind
    if(k=="atom")return(w %in% unlist(m$valuation[[x$name]]))
    if(k=="bottom")return(FALSE)
    if(k=="not")return(!truth(x$args[[1L]],m,w))
    if(k=="and")return(truth(x$args[[1L]],m,w)&&truth(x$args[[2L]],m,w))
    if(k=="or")return(truth(x$args[[1L]],m,w)||truth(x$args[[2L]],m,w))
    if(k=="implies")return(!truth(x$args[[1L]],m,w)||truth(x$args[[2L]],m,w))
    targets<-lapply(Filter(function(e)e[[1L]]==w,m$edges),function(e)e[[2L]])
    for(v in targets){value<-truth(x$args[[1L]],m,v);if(k=="box"&&!value)return(FALSE);if(k=="diamond"&&value)return(TRUE)}
    k=="box"
  };list(truth=truth,state=state)
}
#' @rdname modal_atom
#' @export
evaluate_modal <- function(formula,model,world,max_steps=10000L) {
  .modal_validate(formula);m<-.kripke(model)
  if(!.scalar_string(world)||!world %in% unlist(m$worlds)) .fail("World outside frame")
  if(!all(.modal_atoms(formula) %in% names(m$valuation))) .fail("Missing atom valuation")
  ev<-.modal_evaluator(max_steps);value<-ev$truth(formula,m,world)
  .result(if(value)"ESTABLISHED" else "REFUTED","FINITE_EXACT","finite_modal_truth",limitations=.modal_limit,
    details=list(value=value,world=world,steps_used=ev$state$used),context=list(model_sha256=.data_digest(m)))
}
#' @rdname modal_atom
#' @export
validate_modal_frame <- function(formula,worlds,edges,max_valuations=4096L) {
  .modal_validate(formula);m<-kripke_model(worlds,edges);.int_budget(max_valuations,65536L,"max_valuations")
  atoms<-.modal_atoms(formula);width<-length(m$worlds);size<-length(atoms)*width
  if(size>16L||2^size>max_valuations) .fail("Modal valuation budget exceeded","RESOURCE_LIMIT")
  ev<-.modal_evaluator(1000000L);checked<-0L;checked_worlds<-0L;witness<-NULL
  for(code in seq_len(2^size)-1L) {
    valuation<-.empty_object()
    for(i in seq_along(atoms)) {
      values<-list()
      for(j in seq_len(width))if(bitwAnd(as.integer(code),bitwShiftL(1L,as.integer(size-(i-1L)*width-j)))!=0L)values[[length(values)+1L]]<-m$worlds[[j]]
      valuation[[atoms[[i]]]]<-values
    }
    m$valuation<-valuation;checked<-checked+1L
    for(w in m$worlds){checked_worlds<-checked_worlds+1L;if(!ev$truth(formula,m,w)){witness<-list(world=w,valuation=valuation);break}}
    if(!is.null(witness))break
  }
  .result(if(is.null(witness))"ESTABLISHED" else "REFUTED","FINITE_EXACT","finite_frame_validity",limitations=.modal_limit,
    witness=witness,details=list(valuations_checked=checked,worlds_checked=checked_worlds),context=list(frame_sha256=.data_digest(list(worlds=m$worlds,edges=m$edges))))
}
