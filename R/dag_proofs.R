.dag_view <- function(dag,id=dag$root,info=NULL) {
  if(is.null(info))info<-.dag_info(dag)
  structure(list(graph=dag,index=id,info=info),class="goedel_dag_view")
}
#' @export
`$.goedel_dag_view` <- function(x,name) {
  raw<-unclass(x);node<-raw$graph$nodes[[raw$index+1L]];op<-node$op
  if(name=="kind")return(if(op=="zero")"const" else if(op %in% c("succ","add","mul"))"func" else op)
  if(name=="name")return(if(op=="zero")"zero" else if(op=="succ")"S" else if(op %in% c("add","mul"))op else node$name)
  if(name=="args")return(lapply(node$args,function(i).dag_view(raw$graph,i,raw$info)))
  raw[[name]]
}
.view_dag <- function(x) {raw<-unclass(x);list(schema_version="1.0",nodes=raw$graph$nodes[seq_len(raw$index+1L)],root=raw$index)}
.view_free <- function(x) .numeric_names(.dag_free_at(unclass(x)$info,unclass(x)$index+1L))
.view_require <- function(x,sort) {
  if(!inherits(x,"goedel_dag_view")||unclass(x)$info$types[[unclass(x)$index+1L]]!=sort) .fail(paste("Expected DAG",sort))
  invisible(x)
}
.dag_alpha <- function(left,right) {
  l<-unclass(left);r<-unclass(right)
  # At entry both lexical environments are empty. Identical validated prefixes
  # imply equal root syntax; this shortcut must not be used inside binder traversal.
  if(l$index==r$index&&identical(l$graph$nodes[seq_len(l$index+1L)],
                               r$graph$nodes[seq_len(r$index+1L)]))return(TRUE)
  done<-new.env(hash=TRUE,parent=emptyenv());visited<-0L
  stack<-list(list(a=l$index,b=r$index,le=list(),re=list(),depth=0L))
  envkey<-function(e)paste(names(e),unlist(e),sep="=",collapse=",")
  while(length(stack)) {
    state<-stack[[length(stack)]];stack[[length(stack)]]<-NULL
    key<-paste(state$a,state$b,envkey(state$le),envkey(state$re),sep="|")
    if(exists(key,envir=done,inherits=FALSE))next
    visited<-visited+1L;if(visited>800000L) .fail("DAG comparison context budget exceeded","RESOURCE_LIMIT")
    assign(key,TRUE,envir=done)
    a<-l$graph$nodes[[state$a+1L]];b<-r$graph$nodes[[state$b+1L]]
    if(a$op!=b$op||length(a$args)!=length(b$args))return(FALSE)
    if(a$op=="var") {
      ab<-a$name %in% names(state$le);bb<-b$name %in% names(state$re)
      if(ab!=bb||if(ab)state$le[[a$name]]!=state$re[[b$name]] else a$name!=b$name)return(FALSE)
    } else if(a$op %in% c("forall","exists")) {
      state$depth<-state$depth+1L;state$le[[a$name]]<-state$depth;state$re[[b$name]]<-state$depth
    } else if(a$name!=b$name)return(FALSE)
    for(i in rev(seq_along(a$args)))stack[[length(stack)+1L]]<-list(a=a$args[[i]],b=b$args[[i]],le=state$le,re=state$re,depth=state$depth)
  };TRUE
}
#' Check Scoped Derivations Directly over Arithmetic DAGs
#'
#' This checker uses the same explicit natural-deduction rules and scope discipline
#' as check_scoped_proof, operating on shared arithmetic syntax without expanding
#' it into ordinary Expr trees. Formula, term and template fields contain DAGs.
#' Indexed variable names are used in eigenvariable and substitution fields.
#' Explicit closed DAG axioms are trusted; this entry point has no implicit theory
#' axiom selector. Alpha comparison tracks lexical binding and substitution avoids
#' capture. Success is a native derivation check, not formal-kernel verification.
#' @param steps At most 4096 scoped step records with DAG payloads.
#' @param assumptions A list of trusted formula DAGs.
#' @param axioms A list of trusted closed formula DAGs.
#' @param conclusion Optional expected final formula DAG.
#' @param logic Classical or intuitionistic logic.
#' @return A scoped DAG derivation result with explicit support dependencies.
#' @examples
#' f <- arithmetic_dag(parse_formula("x = x"))
#' step <- list(rule="eq_refl",formula=f,premises=list(),scope=list())
#' check_scoped_dag_proof(list(step))$status
#' @export
check_scoped_dag_proof <- function(steps,assumptions=list(),axioms=list(),conclusion=NULL,logic="classical") {
  .array(steps,"steps");.array(assumptions,"assumptions");.array(axioms,"axioms")
  wrap<-function(dag,sort="formula") {view<-.dag_view(dag);.view_require(view,sort);view}
  converted<-lapply(steps,function(s){if(!is.list(s)) .fail("Invalid DAG proof step");for(field in intersect(names(s),c("formula","template","term")))s[[field]]<-wrap(s[[field]],if(field=="term")"term" else "formula");s})
  context<-new.env(parent=environment(check_scoped_proof))
  context$.require_formula<-function(x).view_require(x,"formula")
  context$.require_term<-function(x).view_require(x,"term")
  context$.formula_list<-function(xs,label){.array(xs,label);if(length(xs)>1000L).fail("Formula list budget exceeded","RESOURCE_LIMIT");for(x in xs).view_require(x,"formula");invisible(xs)}
  context$.joint_signature<-function(expressions)invisible(TRUE)
  context$.name_ok<-.dag_name
  context$free_variables<-.view_free
  context$alpha_equal<-.dag_alpha
  context$substitute_formula<-function(expr,variable,term).dag_view(dag_substitute(.view_dag(expr),variable,.view_dag(term)))
  context$variable<-function(name){if(!.dag_name(name)).fail("Invalid indexed variable");.dag_view(list(schema_version="1.0",nodes=list(list(op="var",name=name,args=list())),root=0L))}
  checker<-check_scoped_proof;environment(checker)<-context
  result<-checker(converted,lapply(assumptions,wrap),lapply(axioms,wrap),conclusion=if(is.null(conclusion))NULL else wrap(conclusion),logic=logic)
  result$claim<-"validity_of_submitted_scoped_dag_proof";result$assumptions<-assumptions
  result$evidence<-list(list(kind="NATIVE_RULE_CHECK",calculus="goedel-nd-scoped-dag-v1",axioms=axioms,theory=NULL))
  if(result$status=="ESTABLISHED")result$witness<-steps
  result
}

#' Compare DAG Syntax Modulo Bound Variable Names
#'
#' Compares the denoted root syntax while tracking lexical binding. Unreachable
#' and duplicated presentation nodes do not affect this comparison. It does not
#' decide semantic equivalence. At most 800000 distinct lexical contexts are visited.
#' @param left,right Arithmetic term or formula DAGs.
#' @return A logical scalar indicating alpha equality.
#' @export
dag_alpha_equal <- function(left,right) .dag_alpha(.dag_view(left),.dag_view(right))
