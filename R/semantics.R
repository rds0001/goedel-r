.object <- function(x,label="object") {
  if(!is.list(x)||(length(x)&&is.null(names(x)))||anyNA(names(x))||anyDuplicated(names(x))) .fail(paste(label,"must be a mapping"))
  if(!length(x)) return(.empty_object())
  x[order(names(x),method="radix")]
}
.array <- function(x,label="array") {if(!is.list(x)||!is.null(names(x))) .fail(paste(label,"must be an array"));x}
.fields <- function(x,fields) is.list(x)&&!anyDuplicated(names(x))&&length(x)==length(fields)&&setequal(names(x),fields)
.canonical_data <- function(x) {
  if(is.list(x)) {if(is.object(x)) x<-unclass(x);x<-lapply(x,.canonical_data);if(!is.null(names(x)))x<-x[order(names(x),method="radix")]};x
}
.data_digest <- function(x) digest::digest(as.character(jsonlite::toJSON(.canonical_data(x),auto_unbox=TRUE,null="null",digits=NA)),algo="sha256",serialize=FALSE)
.labels <- function(x) {
  if(is.character(x)) x<-as.list(x)
  .array(x,"domain");if(!length(x)) .fail("Empty domain")
  if(length(x)>16L) .fail("Domain exceeds 16 elements","RESOURCE_LIMIT")
  if(!all(vapply(x,function(v) .scalar_string(v)&&grepl("^[A-Za-z0-9_]{1,64}$",v),logical(1)))||anyDuplicated(unlist(x))) .fail("Invalid or duplicate domain label")
  as.list(.sorted(unlist(x)))
}
.finite_limit <- "Exact truth concerns only the supplied finite structure, not the natural numbers or consistency of a theory."
#' Exact Evaluation in Explicit Finite Structures
#'
#' A structure supplies a nonempty domain of at most 16 unique ASCII labels and
#' complete interpretations. Function and relation records contain name, arity and
#' table; rows contain args and value. False relation rows must be explicit.
#' Tables are total and contain at most 65536 rows per interpretation category.
#' Numerals denote their binary Horner expansion even in nonstandard finite
#' structures. Evaluation counts visited nodes, including the numeral abbreviation
#' and its expansion. Formulas short-circuit from left to right. A result concerns
#' only the supplied finite structure, never standard arithmetic or consistency.
#' Model checking universally ranges over assignments to each listed formula's
#' free variables; a finite list cannot cover the entire PA induction schema.
#' @param domain A character vector or list of domain labels.
#' @param constants A named list mapping constants to domain labels.
#' @param functions,relations Lists of total interpretation records.
#' @param term A term expression.
#' @param formula A formula expression.
#' @param formulas A list of at most 1000 formulas.
#' @param model A finite structure descriptor.
#' @param assignment A named list assigning all free variables to domain labels.
#' @param max_steps An integer evaluation budget in 1 through 1000000.
#' @return A structure descriptor, or a finite-exact result with value, visited
#' step count, structure fingerprint and the replayable initial assignment where
#' applicable. Quantifier-local values never overwrite free-variable bindings.
#' @examples
#' model <- finite_structure(c("a", "b"))
#' evaluate_formula(forall("x", equal(variable("x"), variable("x"))), model)$status
#' finite_model_check(list(equal(variable("x"), variable("x"))), model)$details
#' @export
finite_structure <- function(domain,constants=.empty_object(),functions=list(),relations=list()) {
  domain<-.labels(domain);constants<-.object(constants,"constants")
  for(n in names(constants)) if(!.name_ok(n)||!.scalar_string(constants[[n]])||!constants[[n]] %in% unlist(domain)) .fail("Invalid constant interpretation")
  tables<-function(records,relation=FALSE) {
    .array(records,"interpretations");if(length(records)>256L) .fail("Signature budget exceeded","RESOURCE_LIMIT")
    out<-list();seen<-character();total<-0L
    for(rec in records) {
      if(!.fields(rec,c("name","arity","table"))||!.name_ok(rec$name)||rec$name %in% seen) .fail("Invalid interpreted symbol")
      seen<-c(seen,rec$name);a<-rec$arity
      if(!is.numeric(a)||is.logical(a)||length(a)!=1L||is.na(a)||!is.finite(a)||a<0||a!=floor(a)) .fail("Invalid interpretation arity")
      if(a>16L||length(domain)^a>65536L) .fail("Table budget exceeded","RESOURCE_LIMIT")
      .array(rec$table,"table");if(length(rec$table)!=length(domain)^a) .fail("Table must be total")
      total<-total+length(rec$table);if(total>65536L) .fail("Table budget exceeded","RESOURCE_LIMIT")
      rows<-list();keys<-character()
      for(row in rec$table) {
        if(!.fields(row,c("args","value"))) .fail("Invalid table row")
        .array(row$args,"table args")
        if(length(row$args)!=a||!all(vapply(row$args,function(v) .scalar_string(v)&&v %in% unlist(domain),logical(1)))) .fail("Invalid table arguments")
        key<-paste(unlist(row$args),collapse="|");if(key %in% keys) .fail("Duplicate table row")
        if(relation) {if(!is.logical(row$value)||length(row$value)!=1L||is.na(row$value)) .fail("Relation value must be boolean")
        } else if(!.scalar_string(row$value)||!row$value %in% unlist(domain)) .fail("Function value outside domain")
        keys<-c(keys,key);rows[[length(rows)+1L]]<-row
      }
      out[[length(out)+1L]]<-list(name=rec$name,arity=as.integer(a),table=rows[order(keys,method="radix")])
    }
    out[order(seen,method="radix")]
  }
  list(schema_version="1.0",domain=domain,constants=constants,functions=tables(functions),relations=tables(relations,TRUE))
}
.structure <- function(model) {
  if(!.fields(model,c("schema_version","domain","constants","functions","relations"))||!identical(model$schema_version,"1.0")) .fail("Unknown finite structure schema")
  finite_structure(model$domain,model$constants,model$functions,model$relations)
}
.evaluator <- function(model,max_steps) {
  model<-.structure(model);.int_budget(max_steps,1000000L);state<-new.env(parent=emptyenv());state$used<-0L
  tick<-function(){state$used<-state$used+1L;if(state$used>max_steps) .fail("Finite evaluation budget exhausted","RESOURCE_LIMIT")}
  functions<-setNames(model$functions,vapply(model$functions,function(r)r$name,""))
  relations<-setNames(model$relations,vapply(model$relations,function(r)r$name,""))
  lookup<-function(records,name,args) {
    rec<-records[[name]];if(is.null(rec)||rec$arity!=length(args)) .fail("Missing interpretation or arity mismatch")
    key<-paste(unlist(args),collapse="|");keys<-vapply(rec$table,function(r)paste(unlist(r$args),collapse="|"),"")
    rec$table[[match(key,keys)]]$value
  }
  signature<-function(x) {
    if(x$kind=="const"&&!x$name %in% names(model$constants)) .fail("Uninterpreted constant")
    if(x$kind %in% c("func","pred")) {
      rec<-if(x$kind=="func")functions[[x$name]] else relations[[x$name]]
      if(is.null(rec)||rec$arity!=length(x$args)) .fail("Missing interpretation or arity mismatch")
    }
    if(x$kind=="num") {
      if(!"zero" %in% names(model$constants)) .fail("Numeral requires zero")
      if(x$name!="0"&&(is.null(functions[["S"]])||functions[["S"]]$arity!=1L)) .fail("Numeral requires unary S")
      if(!x$name %in% c("0","1")&&(is.null(functions[["mul"]])||functions[["mul"]]$arity!=2L)) .fail("Numeral requires binary mul")
    }
    for(a in x$args)signature(a)
  }
  assignment<-function(x,values) {
    values<-.object(values,"assignment")
    for(n in names(values)) if(!.name_ok(n)||!.scalar_string(values[[n]])||!values[[n]] %in% unlist(model$domain)) .fail("Invalid assignment")
    if(!all(free_variables(x) %in% names(values))) .fail("Missing free variable assignment")
    signature(x);values
  }
  term<-function(x,env) {
    tick()
    if(x$kind=="var")return(env[[x$name]])
    if(x$kind=="const")return(model$constants[[x$name]])
    if(x$kind=="num") {
      tick();v<-model$constants[["zero"]];if(x$name=="0")return(v)
      tick();v<-lookup(functions,"S",list(v));bits<-integer();s<-x$name
      while(!s %in% c("0","1")){h<-.dec_half(s);bits<-c(h$remainder,bits);s<-h$value}
      for(bit in bits) {
        for(i in 1:4)tick()
        two<-lookup(functions,"S",list(lookup(functions,"S",list(model$constants[["zero"]]))))
        v<-lookup(functions,"mul",list(two,v));if(bit==1L){tick();v<-lookup(functions,"S",list(v))}
      };return(v)
    }
    lookup(functions,x$name,lapply(x$args,term,env=env))
  }
  formula<-function(x,env) {
    tick();k<-x$kind
    if(k=="bottom")return(list(value=FALSE,assignment=env))
    if(k=="eq")return(list(value=identical(term(x$args[[1L]],env),term(x$args[[2L]],env)),assignment=env))
    if(k=="pred")return(list(value=lookup(relations,x$name,lapply(x$args,term,env=env)),assignment=env))
    if(k=="not"){r<-formula(x$args[[1L]],env);r$value<-!r$value;return(r)}
    if(k %in% c("and","or","implies")) {
      r<-formula(x$args[[1L]],env)
      if(k=="and"&&!r$value)return(r)
      if((k=="or"&&r$value)||(k=="implies"&&!r$value)){r$value<-TRUE;return(r)}
      return(formula(x$args[[2L]],env))
    }
    for(e in model$domain) {
      local<-env;local[[x$name]]<-e;r<-formula(x$args[[1L]],local)
      if((k=="forall"&&!r$value)||(k=="exists"&&r$value))return(r)
    }
    list(value=k=="forall",assignment=env)
  }
  list(model=model,state=state,term=term,formula=formula,assignment=assignment,signature=signature)
}
#' @rdname finite_structure
#' @export
evaluate_term <- function(term,model,assignment=.empty_object(),max_steps=10000L) {
  .require_term(term);ev<-.evaluator(model,max_steps);a<-ev$assignment(term,assignment);value<-ev$term(term,a)
  .result("ESTABLISHED","FINITE_EXACT","finite_term_value",limitations=.finite_limit,
    details=list(value=value,steps_used=ev$state$used),context=list(model_sha256=.data_digest(ev$model)))
}
#' @rdname finite_structure
#' @export
evaluate_formula <- function(formula,model,assignment=.empty_object(),max_steps=10000L) {
  .require_formula(formula);ev<-.evaluator(model,max_steps);a<-ev$assignment(formula,assignment);r<-ev$formula(formula,a)
  .result(if(r$value)"ESTABLISHED" else "REFUTED","FINITE_EXACT","finite_formula_truth",limitations=.finite_limit,
    witness=list(assignment=.object(a)),details=list(value=r$value,steps_used=ev$state$used),context=list(model_sha256=.data_digest(ev$model)))
}
#' @rdname finite_structure
#' @export
finite_model_check <- function(formulas,model,max_steps=10000L) {
  .formula_list(formulas,"formulas");ev<-.evaluator(model,max_steps)
  for(f in formulas)ev$signature(f)
  checked<-0L;witness<-NULL
  for(i in seq_along(formulas)) {
    f<-formulas[[i]];vars<-free_variables(f)
    visit<-function(k,env) {
      if(k>length(vars)) {r<-ev$formula(f,env);if(!r$value)witness<<-list(formula_index=i,assignment=.object(env));return()}
      for(e in ev$model$domain){env[[vars[[k]]]]<-e;visit(k+1L,env);if(!is.null(witness))break}
    }
    visit(1L,.empty_object());checked<-checked+1L;if(!is.null(witness))break
  }
  .result(if(is.null(witness))"ESTABLISHED" else "REFUTED","FINITE_EXACT","finite_model_of_list",limitations=.finite_limit,
    witness=witness,details=list(checked_formulas=checked,steps_used=ev$state$used,value=is.null(witness)),context=list(model_sha256=.data_digest(ev$model)))
}
# Canonical primitive JSON without per-node S4 dispatch. Public payloads contain
# only JSON scalars/lists. Complex string escaping still delegates to jsonlite.
.fast_json <- function(x) {
  quote<-function(s) {
    if(!grepl('"',s,fixed=TRUE)&&!grepl("\\",s,fixed=TRUE)&&!grepl("[[:cntrl:]]",s))paste0('"',s,'"') else .json_string(s)
  }
  walk<-function(v) {
    if(is.null(v))return("null")
    if(is.list(v)) {
      if(.fields(v,c("schema_version","nodes","root"))&&identical(v$schema_version,"1.0")&&is.list(v$nodes)&&is.null(names(v$nodes))&&.register_integer(v$root,0L,200000L)&&all(vapply(v$nodes,function(n).fields(n,c("op","name","args"))&&.scalar_string(n$op)&&.scalar_string(n$name)&&is.list(n$args)&&is.null(names(n$args))&&all(vapply(n$args,.register_integer,logical(1),lower=0L,upper=200000L)),logical(1)))) {
        nodes<-vapply(v$nodes,function(n)paste0('{"args":[',paste(as.integer(unlist(n$args)),collapse=","),'],"name":',quote(n$name),',"op":',quote(n$op),'}'),"")
        return(paste0('{"nodes":[',paste(nodes,collapse=","),'],"root":',as.integer(v$root),',"schema_version":"1.0"}'))
      }
      if(is.null(names(v)))return(paste0("[",paste(vapply(v,walk,""),collapse=","),"]"))
      ns<-sort(names(v),method="radix")
      return(paste0("{",paste(vapply(ns,function(n)paste0(quote(n),":",walk(v[[n]])),""),collapse=","),"}"))
    }
    if(length(v)!=1L||is.na(v)) .fail("Canonical JSON requires nonmissing scalar values")
    if(is.character(v))return(quote(v))
    if(is.logical(v))return(if(v)"true" else "false")
    if(is.numeric(v)&&is.finite(v))return(if(v==floor(v)&&abs(v)<=9007199254740991)formatC(v,format="f",digits=0) else as.character(jsonlite::toJSON(v,auto_unbox=TRUE,digits=NA)))
    .fail("Unsupported canonical JSON value")
  };walk(x)
}
