#' Parse and Format Explicit First-Order Formula Text
#'
#' The ASCII grammar uses !, &, |, ->, =, + and *, with multiplication binding
#' most tightly and implication associating to the right. Quantifiers are written
#' forall x. or exists x.; false denotes bottom. Constants have an explicit @
#' prefix; decimal numeral abbreviations are distinct from @zero. The parser
#' never evaluates R code. Formatting preserves syntax and bound variable names.
#' @param text One formula string, at most 65536 bytes.
#' @param expr A term or formula to format.
#' @return The parser returns a formula expression; formatting returns text.
#' @examples
#' f <- parse_formula("forall x. (x + 0 = x) -> !(x = 1)")
#' alpha_equal(parse_formula(format_formula(f)), f)
#' @export
parse_formula <- function(text) {
  if(!.scalar_string(text)) .fail("Expected formula text")
  if(nchar(text,type="bytes")>65536L) .fail("Text exceeds byte budget","RESOURCE_LIMIT")
  tokens <- character(); rest <- text
  while(nzchar(rest)) {
    rest <- sub("^[ \t\r\n]+","",rest)
    if(!nzchar(rest)) break
    match <- regexpr("^(->|[A-Za-z][A-Za-z0-9_]*|[0-9]+|[@!&|=+*().,])",rest,perl=TRUE)
    if(match[1L]!=1L) .fail("Invalid formula token")
    token <- regmatches(rest,match); tokens <- c(tokens,token); rest <- substring(rest,nchar(token)+1L)
    if(length(tokens)>4096L) .fail("Too many tokens","RESOURCE_LIMIT")
  }
  pos <- 1L; depth <- 0L
  peek <- function(offset=0L) if(pos+offset<=length(tokens)) tokens[[pos+offset]] else ""
  take <- function(expected=NULL) { t <- peek(); if(!nzchar(t)||(!is.null(expected)&&t!=expected)) .fail("Unexpected formula token");pos<<-pos+1L;t }
  enter <- function() {depth<<-depth+1L;if(depth>64L) .fail("Parser nesting too deep","RESOURCE_LIMIT")}
  leave <- function() depth<<-depth-1L
  term_atom <- function() {
    enter(); on.exit(leave()); t <- peek()
    if(t=="(") {take(); x<-term_add();take(")");return(x)}
    if(t=="@") {take();return(constant(take()))}
    if(grepl("^[0-9]+$",t)) {take();return(numeral(t))}
    if(!.name_ok(t)) .fail("Expected term")
    take()
    if(peek()!="(") return(variable(t))
    take(); args<-list()
    if(peek()!=")") repeat {args[[length(args)+1L]]<-term_add();if(peek()!=",")break;take()}
    take(")");function_term(t,args)
  }
  term_mul <- function() {x<-term_atom();while(peek()=="*"){take();x<-multiply(x,term_atom())};x}
  term_add <- function() {x<-term_mul();while(peek()=="+"){take();x<-add(x,term_mul())};x}
  atom <- function() {
    enter(); on.exit(leave()); t<-peek()
    if(t=="!"){take();return(negate(atom()))}
    if(t %in% c("forall","exists") && .name_ok(peek(1L)) && peek(2L)==".") {
      take();v<-take();take(".");body<-impl();return(if(t=="forall")forall(v,body) else exists_formula(v,body))
    }
    if(t=="false" && peek(1L)!="(" && peek(1L)!="="){take();return(bottom())}
    old<-pos
    lhs<-tryCatch(term_add(),goedel_error=function(e){if(e$code=="RESOURCE_LIMIT")stop(e);NULL})
    if(!is.null(lhs)&&peek()=="="){take();return(equal(lhs,term_add()))}
    pos<<-old
    if(peek()=="("){take();f<-impl();take(")");return(f)}
    name<-take();if(!.name_ok(name)) .fail("Expected predicate")
    args<-list()
    if(peek()=="("){take();if(peek()!=")")repeat{args[[length(args)+1L]]<-term_add();if(peek()!=",")break;take()};take(")")}
    predicate(name,args)
  }
  conj <- function(){x<-atom();while(peek()=="&"){take();x<-conjunction(x,atom())};x}
  disj <- function(){x<-conj();while(peek()=="|"){take();x<-disjunction(x,conj())};x}
  impl <- function(){enter();on.exit(leave());x<-disj();if(peek()=="->"){take();x<-implication(x,impl())};x}
  out<-impl();if(pos<=length(tokens)) .fail("Trailing formula tokens");.require_formula(out);out
}
#' @rdname parse_formula
#' @export
format_formula <- function(expr) {
  .validate(expr)
  fmt <- function(x) {
    a<-lapply(x$args,fmt)
    switch(x$kind,var=x$name,const=paste0("@",x$name),num=x$name,
      func=if(x$name %in% c("add","mul")&&length(a)==2L) paste0("(",a[[1L]],if(x$name=="add")" + " else " * ",a[[2L]],")") else paste0(x$name,"(",paste(a,collapse=","),")"),
      pred=paste0(x$name,"(",paste(a,collapse=","),")"),bottom="false",
      eq=paste0("(",a[[1L]]," = ",a[[2L]],")"),not=paste0("!(",a[[1L]],")"),
      and=paste0("(",a[[1L]]," & ",a[[2L]],")"),or=paste0("(",a[[1L]]," | ",a[[2L]],")"),
      implies=paste0("(",a[[1L]]," -> ",a[[2L]],")"),
      forall=paste0("(forall ",x$name,". ",a[[1L]],")"),exists=paste0("(exists ",x$name,". ",a[[1L]],")"))
  };fmt(expr)
}
