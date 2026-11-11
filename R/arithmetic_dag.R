.dag_ops <- c("zero","var","succ","add","mul","eq","not","and","or","implies","exists","forall","bottom","num")
.dag_macro_ops <- c(.dag_ops,"num","lt","bexists","bforall")
.big_nat <- function(x,max_digits=5000000L) {
  if(!.scalar_string(x)||!grepl("^(0|[1-9][0-9]*)$",x)) .fail("Expected exact canonical natural number")
  if(nchar(x)>max_digits) .fail("Natural number digit budget exceeded","RESOURCE_LIMIT")
  gmp::as.bigz(x)
}
.dag_name <- function(x) .scalar_string(x)&&grepl("^x(0|[1-9][0-9]*)$",x)&&nchar(x)<=4097L
.numeric_names <- function(xs) {xs<-unique(xs);if(!length(xs))return(character());xs[order(nchar(xs),xs,method="radix")]}
.dag_info <- function(dag,bounded=FALSE,formula=FALSE) {
  if(!is.logical(bounded)||length(bounded)!=1L||is.na(bounded)||!.fields(dag,c("schema_version","nodes","root"))||!identical(dag$schema_version,"1.0")) .fail("Invalid arithmetic DAG envelope")
  .array(dag$nodes,"DAG nodes");n<-length(dag$nodes)
  if(!n) .fail("DAG requires nodes")
  if(n>200000L) .fail("DAG node budget exceeded","RESOURCE_LIMIT")
  root<-dag$root;if(!is.numeric(root)||is.logical(root)||length(root)!=1L||is.na(root)||!is.finite(root)||root!=floor(root)||root!=n-1L) .fail("Invalid DAG root")
  types<-character(n);free<-vector("list",n);counts<-vector("list",n);inventory<-character();name_index<-new.env(hash=TRUE,parent=emptyenv())
  arity<-c(zero=0L,var=0L,num=0L,bottom=0L,succ=1L,add=2L,mul=2L,eq=2L,lt=2L,not=1L,and=2L,or=2L,implies=2L,exists=1L,forall=1L,bexists=2L,bforall=2L)
  for(i in seq_len(n)) {
    nd<-dag$nodes[[i]]
    if(!.fields(nd,c("op","name","args"))||!.scalar_string(nd$op)||!nd$op %in% (if(bounded).dag_macro_ops else .dag_ops)||!.scalar_string(nd$name)) .fail("Invalid DAG node operation")
    .array(nd$args,"DAG args");if(length(nd$args)!=arity[[nd$op]]) .fail("Invalid DAG arity")
    for(a in nd$args)if(!is.numeric(a)||is.logical(a)||length(a)!=1L||is.na(a)||!is.finite(a)||a!=floor(a)||a<0||a>=i-1L) .fail("DAG references must point backward")
    op<-nd$op;name<-nd$name;args<-as.integer(unlist(nd$args))+1L
    if(op %in% c("var","exists","forall","bexists","bforall")) {if(!.dag_name(name)) .fail("DAG variables require natural indexed names")
      if(!exists(name,envir=name_index,inherits=FALSE)){if(length(inventory)>=4096L) .fail("DAG variable budget exceeded","RESOURCE_LIMIT");assign(name,length(inventory),envir=name_index);inventory<-c(inventory,name)}
    } else if(op=="num") .big_nat(name) else if(name!="") .fail("Unexpected DAG name")
    wanted<-if(op %in% c("succ","add","mul","eq","lt"))rep("term",length(args)) else if(op %in% c("bexists","bforall"))c("term","formula") else rep("formula",length(args))
    if(!identical(types[args],wanted)) .fail("DAG sort mismatch")
    types[[i]]<-if(op %in% c("zero","var","num","succ","add","mul"))"term" else "formula"
    vars<-raw()
    for(a in args){other<-free[[a]];width<-max(length(vars),length(other));length(vars)<-width;length(other)<-width;vars<-as.raw(bitwOr(as.integer(vars),as.integer(other)))}
    if(op %in% c("var","exists","forall","bexists","bforall")) {
      ni<-get(name,envir=name_index,inherits=FALSE);byte<-ni%/%8L+1L;mask<-bitwShiftL(1L,ni%%8L)
      if(length(vars)<byte)length(vars)<-byte
      if(op %in% c("bexists","bforall")&&length(free[[args[[1L]]]])>=byte&&bitwAnd(as.integer(free[[args[[1L]]]][byte]),mask)!=0L) .fail("Bound variable occurs in its own bound")
      vars[byte]<-as.raw(if(op=="var")bitwOr(as.integer(vars[byte]),mask) else bitwAnd(as.integer(vars[byte]),bitwXor(255L,mask)))
    }
    free[[i]]<-vars;count<-gmp::as.bigz(1);for(a in args)count<-count+counts[[a]]
    if(gmp::sizeinbase(count,2L)>16384L) .fail("DAG expansion-count budget exceeded","RESOURCE_LIMIT")
    counts[[i]]<-count
  }
  if(formula&&types[[root+1L]]!="formula") .fail("DAG root must be a formula")
  bits<-free[[root+1L]]
  selected<-vapply(seq_along(inventory)-1L,function(i){b<-i%/%8L+1L;length(bits)>=b&&bitwAnd(as.integer(bits[b]),bitwShiftL(1L,i%%8L))!=0L},logical(1))
  list(statistics=list(nodes=n,root_sort=types[[root+1L]],expanded_nodes=as.character(counts[[root+1L]]),free_variables=as.list(.numeric_names(inventory[selected]))),types=types,free=free,inventory=inventory,name_index=name_index)
}
#' Validate and Serialize Explicit Arithmetic Formula DAGs
#'
#' Arithmetic DAGs share literal subexpressions without introducing uninterpreted
#' predicates. Nodes have op, name and zero-based backward args; the envelope has
#' schema_version, nodes and a zero-based root. The base signature contains only
#' zero, successor, addition, multiplication, equality and logical operators.
#' Numerals are explicit conservative abbreviations in the base profile. With
#' bounded=TRUE, less-than and bounded-quantifier abbreviations are also permitted. Variables have indexed names x0, x1, and so on. Validation checks
#' sorts and lexical free variables. Expanded counts use exact integers and mean
#' literal unsharing; each numeral or bounded-notation node still counts once.
#' The separate DAG profile permits up to 200000 shared nodes; ordinary Expr limits
#' are unchanged. A validated DAG is symbolic syntax, not a verified theorem.
#' @param dag An arithmetic DAG descriptor.
#' @param bounded Whether to permit the documented conservative abbreviations.
#' @return Validation returns node count, exact expanded count and free variables;
#' serialization returns canonical JSON and fingerprint returns SHA-256.
#' @examples
#' d <- list(schema_version="1.0", nodes=list(
#'   list(op="zero",name="",args=list()),
#'   list(op="eq",name="",args=list(0L,0L))),root=1L)
#' validate_arithmetic_dag(d)
#' dag_fingerprint(d)
#' @export
validate_arithmetic_dag <- function(dag,bounded=FALSE) .dag_info(dag,bounded)$statistics
#' @rdname validate_arithmetic_dag
#' @export
serialize_arithmetic_dag <- function(dag,bounded=FALSE) {
  validate_arithmetic_dag(dag,bounded)
  nodes<-vapply(dag$nodes,function(n)paste0('{"args":[',paste(as.integer(unlist(n$args)),collapse=","),'],"name":"',n$name,'","op":"',n$op,'"}'),"")
  paste0('{"nodes":[',paste(nodes,collapse=","),'],"root":',as.integer(dag$root),',"schema_version":"1.0"}')
}
#' @rdname validate_arithmetic_dag
#' @export
dag_fingerprint <- function(dag,bounded=FALSE) digest::digest(serialize_arithmetic_dag(dag,bounded),algo="sha256",serialize=FALSE)
.dag_builder <- function() {
  state<-new.env(parent=emptyenv());state$nodes<-new.env(hash=TRUE,parent=emptyenv());state$count<-0L;state$index<-new.env(hash=TRUE,parent=emptyenv())
  node<-function(op,name="",args=list()) {
    key<-paste(op,name,paste(as.integer(unlist(args)),collapse=","),sep="|")
    if(nchar(key,type="bytes")>8000L)key<-paste0("sha256:",digest::digest(key,algo="sha256",serialize=FALSE))
    basekey<-key;collision<-0L
    while(exists(key,envir=state$index,inherits=FALSE)) {
      id<-get(key,envir=state$index,inherits=FALSE);prior<-get(as.character(id),envir=state$nodes,inherits=FALSE)
      if(prior$op==op&&prior$name==name&&identical(as.integer(unlist(prior$args)),as.integer(unlist(args))))return(id)
      collision<-collision+1L;key<-paste0(basekey,":",collision)
    }
    if(state$count>=200000L) .fail("DAG node budget exceeded","RESOURCE_LIMIT")
    id<-state$count;assign(as.character(id),list(op=op,name=name,args=as.list(as.integer(unlist(args)))),envir=state$nodes);state$count<-state$count+1L
    assign(key,id,envir=state$index);id
  }
  export<-function(root) {
    force(root)
    seen<-rep(FALSE,state$count);stack<-root
    while(length(stack)){i<-tail(stack,1L);stack<-head(stack,-1L);if(seen[[i+1L]])next;seen[[i+1L]]<-TRUE;stack<-c(stack,unlist(get(as.character(i),envir=state$nodes,inherits=FALSE)$args))}
    ids<-which(seen);map<-integer(length(seen));map[ids]<-seq_along(ids)-1L
    nodes<-lapply(ids,function(i){nd<-get(as.character(i-1L),envir=state$nodes,inherits=FALSE);nd$args<-lapply(nd$args,function(a)map[[a+1L]]);nd})
    list(schema_version="1.0",nodes=nodes,root=map[[root+1L]])
  }
  list(node=node,export=export,state=state)
}
.expr_dag_name <- function(name) {
  value<-gmp::as.bigz(1);for(b in as.integer(charToRaw(name)))value<-value*256L+b
  paste0("x",as.character(value))
}
#' Convert Ordinary Arithmetic Syntax to a Shared Formula DAG
#'
#' Every ordinary variable name maps injectively to xN, where N is the big-endian
#' integer of a sentinel byte one followed by the ASCII name bytes. This mapping
#' is independent of surrounding formulas and preserves identity under composition.
#' Compiler-generated DAG names already use their indexed namespace and are not
#' encoded again. Bottom remains an explicit logical falsum node.
#' @param expr An ordinary arithmetic term or formula.
#' @return An arithmetic DAG with conservative numeral abbreviations if present.
#' @examples
#' d <- arithmetic_dag(parse_formula("forall x. x = x"))
#' validate_arithmetic_dag(d, bounded=TRUE)
#' @export
arithmetic_dag <- function(expr) {
  .validate(expr);if(!.arithmetic_ok(expr)) .fail("Expected arithmetic signature")
  b<-.dag_builder()
  walk<-function(x) {
    args<-lapply(x$args,walk);k<-x$kind
    if(k=="bottom")return(b$node("bottom"))
    if(k=="const")return(b$node("zero"))
    if(k=="func")return(b$node(switch(x$name,S="succ",add="add",mul="mul"),args=args))
    name<-if(k %in% c("var","forall","exists")) .expr_dag_name(x$name) else if(k=="num")x$name else ""
    b$node(k,name,args)
  };out<-b$export(walk(expr));validate_arithmetic_dag(out,TRUE);out
}
#' Substitute Arithmetic DAG Terms Without Variable Capture
#'
#' General substitution replaces free occurrences and renames conflicting binders.
#' Fresh indexed names are chosen above every index in both inputs. The replacement
#' DAG must have a term root; the source may be a term or formula.
#' No semantic equivalence or representability theorem is asserted by this purely
#' symbolic transformation.
#' @param dag A formula DAG, permitting conservative bounded notation.
#' @param variable An indexed variable name xN.
#' @param term_dag A DAG with a term root.
#' @return A capture-avoiding arithmetic term or formula DAG.
#' @export
dag_substitute <- function(dag,variable,term_dag) {
  info<-.dag_info(dag,TRUE);ti<-.dag_info(term_dag,TRUE,FALSE)
  if(!.dag_name(variable)||ti$types[[term_dag$root+1L]]!="term") .fail("Expected indexed variable and term DAG")
  b<-.dag_builder();mapping<-integer(length(term_dag$nodes))
  for(i in seq_along(term_dag$nodes)){nd<-term_dag$nodes[[i]];mapping[[i]]<-b$node(nd$op,nd$name,lapply(nd$args,function(a)mapping[[a+1L]]))}
  replacement<-mapping[[term_dag$root+1L]];replacement_free<-.dag_free_at(ti,term_dag$root+1L)
  names_all<-vapply(c(dag$nodes,term_dag$nodes),function(n)if(n$op %in% c("var","exists","forall","bexists","bforall"))n$name else "","")
  names_all<-.numeric_names(names_all[nzchar(names_all)]);last<-if(length(names_all)) .big_nat(substring(tail(names_all,1L),2L)) else gmp::as.bigz(0)
  fresh<-function(){last<<-last+1L;paste0("x",as.character(last))}
  key<-function(i,env,active)paste(i,active,paste(names(env),unlist(env),sep="=",collapse=","),sep="|")
  done<-new.env(hash=TRUE,parent=emptyenv());visited<-0L;stack<-list(list(index=dag$root,env=list(),active=TRUE,stage=0L));root_key<-key(dag$root,list(),TRUE)
  while(length(stack)) {
    frame<-stack[[length(stack)]];stack[[length(stack)]]<-NULL;k<-key(frame$index,frame$env,frame$active)
    if(exists(k,envir=done,inherits=FALSE))next
    nd<-dag$nodes[[frame$index+1L]]
    if(frame$stage==1L) {
      args<-lapply(frame$children,function(child)get(key(child$index,child$env,child$active),envir=done,inherits=FALSE))
      assign(k,b$node(nd$op,frame$name,args),envir=done);next
    }
    visited<-visited+1L;if(visited>800000L) .fail("DAG substitution context budget exceeded","RESOURCE_LIMIT")
    if(nd$op=="var") {
      value<-if(frame$active&&nd$name==variable)replacement else b$node("var",if(nd$name %in% names(frame$env))frame$env[[nd$name]] else nd$name)
      assign(k,value,envir=done);next
    }
    children<-list();newname<-nd$name
    binder<-nd$op %in% c("exists","forall","bexists","bforall")
    if(binder) {
      body<-tail(nd$args,1L)[[1L]]
      replaced_here<-.dag_has_free(info,body+1L,variable)||
        (nd$op %in% c("bexists","bforall")&&.dag_has_free(info,nd$args[[1L]]+1L,variable))
      if(frame$active&&nd$name!=variable&&nd$name %in% replacement_free&&replaced_here)newname<-fresh()
    }
    for(j in seq_along(nd$args)) {
      env<-frame$env;active<-frame$active
      if(binder&&j==length(nd$args)){if(newname==nd$name)env[[nd$name]]<-NULL else env[[nd$name]]<-newname;if(length(env))env<-env[order(names(env),method="radix")];if(nd$name==variable)active<-FALSE}
      children[[j]]<-list(index=nd$args[[j]],env=env,active=active,stage=0L)
    }
    frame$stage<-1L;frame$name<-newname;frame$children<-children;stack[[length(stack)+1L]]<-frame
    for(child in rev(children))stack[[length(stack)+1L]]<-child
  }
  result<-b$export(get(root_key,envir=done,inherits=FALSE));validate_arithmetic_dag(result,TRUE);result
}

.dag_free_at <- function(info,index) {
  bits<-info$free[[index]]
  info$inventory[vapply(seq_along(info$inventory)-1L,function(i){b<-i%/%8L+1L;length(bits)>=b&&bitwAnd(as.integer(bits[b]),bitwShiftL(1L,i%%8L))!=0L},logical(1))]
}

.dag_has_free <- function(info,index,name) {
  if(!exists(name,envir=info$name_index,inherits=FALSE))return(FALSE)
  i<-get(name,envir=info$name_index,inherits=FALSE);b<-i%/%8L+1L;bits<-info$free[[index]]
  length(bits)>=b&&bitwAnd(as.integer(bits[b]),bitwShiftL(1L,i%%8L))!=0L
}
