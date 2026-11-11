.inference_rules <- function() {
  path<-system.file("extdata","inference_rules.json",package="goedel")
  if(!nzchar(path)) .fail("Inference resource unavailable")
  list(data=jsonlite::fromJSON(path,simplifyVector=FALSE),sha256=digest::digest(file=path,algo="sha256"))
}
.inference_equal <- function(a,b) identical(.ascii_json(a),.ascii_json(b))
.inference_fields <- function(x,fields) is.list(x)&&!anyDuplicated(names(x))&&setequal(names(x),fields)
.inference_context <- function(context) {
  if(!.inference_fields(context,c("schema_version","theory_id","metatheory_id","level","assumptions","predicate_identity")) ||
     !identical(context$schema_version,"1.0")||!identical(context$level,"META")) .fail("Invalid inference context or object/metatheory level")
  inference_context(context$theory_id,context$assumptions,context$metatheory_id,context$predicate_identity)
}
.inference_fact <- function(property,value,context) {
  if(!.scalar_string(property)||!nzchar(property)||nchar(property)>128L||!is.logical(value)||length(value)!=1L||is.na(value))
    .fail("A property label and boolean polarity are required")
  list(property=property,value=value,level="META",theory_id=context$theory_id,
       metatheory_id=context$metatheory_id,predicate_identity=context$predicate_identity)
}
.inference_predicate_reviewed <- function(context) {
  if(is.null(context$predicate_identity))return(FALSE)
  path<-system.file("extdata","provability_representation.json",package="goedel")
  if(!nzchar(path))return(FALSE)
  review<-.metatheorem_review();resource<-review$bundle;hbl<-resource$hbl_review
  isTRUE(review$pinned)&&identical(context$theory_id,context$predicate_identity$theory_id)&&
    .inference_equal(context$predicate_identity,resource$identity)&&
    .inference_equal(context$predicate_identity,provability_identity())&&
    identical(resource$review$status,"INDEPENDENTLY_CHECKED")&&isTRUE(resource$review$hbl_schemas_reviewed)&&
    identical(hbl$status,"INDEPENDENTLY_CHECKED")&&.inference_equal(hbl$predicate_identity,context$predicate_identity)&&
    all(vapply(c("D1","D2","D3"),function(n)identical(hbl$conditions[[n]]$status,"INDEPENDENTLY_CHECKED"),logical(1)))
}
.inference_usable <- function(rule,context) {
  if(!is.null(rule$statement_id)) {
    statements<-Filter(function(s)identical(s$id,rule$statement_id),.catalogue()$statements)
    if(length(statements)!=1L)return(FALSE)
    statement<-statements[[1L]];evidence<-statement$evidence
    if((!is.null(statement$active)&&!isTRUE(statement$active))||
       !identical(evidence$kind,"LITERATURE_RESULT")||!identical(evidence$review_status,"REVIEWED")||
       !isTRUE(evidence$verification_status %in% c("INDEPENDENTLY_CHECKED","FORMALLY_VERIFIED"))||
       any(!vapply(statement$requirements,function(name)isTRUE(rule$premises[[name]]),logical(1))))return(FALSE)
  }
  isTRUE(rule$active)&&identical(rule$review_status,"REVIEWED")&&
    isTRUE(rule$verification_status %in% c("INDEPENDENTLY_CHECKED","FORMALLY_VERIFIED"))&&
    (!isTRUE(rule$requires_predicate)||.inference_predicate_reviewed(context))
}
.inference_result <- function(status,context,witness,details,dependencies=list()) {
  .result(status,"CATALOGUE_INFERENCE","Conditional typed catalogue consequence",context$assumptions,list(),
          "Conditional catalogue inference; declarations and literature premises are not proved by this replay.",
          witness,details,context,dependencies)
}

#' Typed Conditional Catalogue Inference
#'
#' Context declarations remain unverified assumptions. Inference rules retain
#' their mathematical level, theory and metatheory identity, evidence status and
#' predicate identity. Witnesses bind current catalogue and rule hashes. The
#' checker independently replays each rule; graph reachability is insufficient.
#' Failed finite inference returns UNKNOWN. Replay of a malformed or stale chain
#' never establishes a mathematical conclusion. Predicate-dependent inference
#' requires an installed, independently reviewed exact representation identity.
#' Its theory must equal the query theory. Withdrawing linked literature evidence
#' or adding an unsupported hypothesis disables new inference and old replay.
#' @param theory A nonempty theory label.
#' @param assumptions Named list of boolean declarations.
#' @param metatheory A nonempty metatheory label.
#' @param predicate_identity Optional exact representation identity record.
#' @param property A property label.
#' @param value Boolean conclusion polarity.
#' @param context A context from \code{inference_context}.
#' @param max_steps Operational inference-step limit, from 1 to 4096.
#' @param witness An explicit catalogue derivation witness.
#' @return Contexts and rules are lists. Inference/replay returns a structured
#' result; explanations retain the provenance of every step.
#' @examples
#' context <- inference_context("T", list(consistent = TRUE))
#' infer("consistent", TRUE, context)
#' list_inference_rules()
#' @export
inference_context <- function(theory,assumptions=list(),metatheory="ordinary_classical_metamathematics",predicate_identity=NULL) {
  declared<-theory_context(theory,assumptions)
  if(!.scalar_string(metatheory)||!nzchar(metatheory)||nchar(metatheory)>128L) .fail("Metatheory must be a nonempty label of at most 128 characters")
  if(!is.null(predicate_identity)&&(!is.list(predicate_identity)||is.null(names(predicate_identity)))) .fail("Predicate identity must be a record or NULL")
  list(schema_version="1.0",theory_id=theory,metatheory_id=metatheory,level="META",
       assumptions=declared$assumptions,predicate_identity=predicate_identity)
}
#' @rdname inference_context
#' @export
list_inference_rules <- function() {
  rules<-.inference_rules()$data$rules
  rules[order(vapply(rules,function(r)r$id,""),method="radix")]
}
#' @rdname inference_context
#' @export
check_derivation <- function(witness,context=NULL) {
  if(!.inference_fields(witness,c("schema_version","context","catalogue_sha256","rules_sha256","steps","goal"))||
     !identical(witness$schema_version,"1.0")) .fail("Malformed catalogue derivation envelope")
  stored<-.inference_context(witness$context)
  checked<-if(is.null(context))stored else .inference_context(context)
  fail<-function(reason,index=NULL).inference_result("REFUTED",checked,NULL,list(reason=reason,invalid_step=index))
  if(!.inference_equal(stored,checked))return(fail("CONTEXT_IDENTITY_MISMATCH"))
  resource<-.inference_rules()
  if(!identical(witness$catalogue_sha256,catalogue_manifest()$sha256)||!identical(witness$rules_sha256,resource$sha256))
    return(fail("STALE_RESOURCE_HASH"))
  steps<-witness$steps
  if(!is.list(steps)||(!is.null(names(steps))&&length(steps))) .fail("Derivation steps must be an array")
  if(length(steps)>4096L).fail("Derivation exceeds 4096 steps","RESOURCE_LIMIT")
  integer_scalar<-function(x)is.numeric(x)&&length(x)==1L&&!is.na(x)&&is.finite(x)&&x==floor(x)
  goal<-witness$goal
  if(!integer_scalar(goal)||goal<1L||goal>length(steps))return(fail("INVALID_GOAL_REFERENCE"))
  rules<-resource$data$rules;names(rules)<-vapply(rules,function(r)r$id,"")
  known<-list();dependencies<-list()
  for(index in seq_along(steps)) {
    step<-steps[[index]]
    if(!.inference_fields(step,c("fact","source","rule","premises"))) .fail("Malformed derivation step")
    fact<-step$fact
    if(!.inference_fields(fact,c("property","value","level","theory_id","metatheory_id","predicate_identity"))) .fail("Malformed typed fact")
    if(!.inference_equal(fact,.inference_fact(fact$property,fact$value,checked)))return(fail("FACT_CONTEXT_OR_LEVEL_MISMATCH",index))
    refs<-step$premises
    if(!is.list(refs)||(!is.null(names(refs))&&length(refs))||any(!vapply(refs,function(r)integer_scalar(r)&&r>=1L&&r<index,logical(1))))
      return(fail("INVALID_PREMISE_REFERENCE",index))
    prop<-fact$property;value<-fact$value
    if(prop %in% names(known)&&!identical(known[[prop]],value))
      return(.inference_result("INCONSISTENT_CONTEXT",checked,NULL,list(reason="CONTRADICTORY_FACTS",property=prop)))
    if(identical(step$source,"DECLARATION")) {
      if(!is.null(step$rule)||length(refs)||!identical(checked$assumptions[[prop]],value))return(fail("UNDECLARED_PREMISE",index))
      dependencies[[length(dependencies)+1L]]<-list(property=prop,value=value,source="DECLARED_NOT_VERIFIED")
    } else if(identical(step$source,"RULE")) {
      if(!.scalar_string(step$rule)||!step$rule %in% names(rules))return(fail("RULE_UNAVAILABLE_OR_UNREVIEWED",index))
      rule<-rules[[step$rule]]
      if(!.inference_usable(rule,checked))return(fail("RULE_UNAVAILABLE_OR_UNREVIEWED",index))
      if(!.inference_equal(rule$conclusion,list(property=prop,value=value)))return(fail("RULE_CONCLUSION_MISMATCH",index))
      required<-sort(names(rule$premises),method="radix")
      if(length(refs)!=length(required))return(fail("RULE_PREMISES_MISMATCH",index))
      for(i in seq_along(required)) {
        name<-required[[i]]
        if(!.inference_equal(steps[[refs[[i]]]]$fact,.inference_fact(name,rule$premises[[name]],checked)))
          return(fail("RULE_PREMISES_MISMATCH",index))
      }
    } else return(fail("UNKNOWN_STEP_SOURCE",index))
    known[[prop]]<-value
  }
  .inference_result("ESTABLISHED",checked,witness,list(reason="VALID_CONDITIONAL_DERIVATION",conclusion=steps[[goal]]$fact),dependencies)
}
#' @rdname inference_context
#' @export
infer <- function(property,value,context,max_steps=256L) {
  checked<-.inference_context(context);goal<-.inference_fact(property,value,checked)
  if(!is.numeric(max_steps)||length(max_steps)!=1L||is.na(max_steps)||!is.finite(max_steps)||max_steps!=floor(max_steps)||max_steps<1L||max_steps>4096L)
    .fail("max_steps must be an integer from 1 to 4096")
  resource<-.inference_rules();rules<-list_inference_rules();steps<-list();known<-list()
  admit<-function(prop,polarity,source,rule=NULL,premises=list()) {
    if(!prop %in% names(known)) {
      known[[prop]]<<-length(steps)+1L
      steps[[length(steps)+1L]]<<-list(fact=.inference_fact(prop,polarity,checked),source=source,rule=rule,premises=premises)
    }
  }
  for(prop in sort(names(checked$assumptions),method="radix")) {
    if(length(steps)>=max_steps)return(.inference_result("UNKNOWN",checked,NULL,list(reason="BOUND_EXHAUSTED")))
    admit(prop,checked$assumptions[[prop]],"DECLARATION")
  }
  progress<-TRUE
  while(progress) {
    progress<-FALSE
    for(rule in rules) {
      if(!.inference_usable(rule,checked))next
      available<-all(vapply(names(rule$premises),function(p)p %in% names(known)&&identical(steps[[known[[p]]]]$fact$value,rule$premises[[p]]),logical(1)))
      if(!available)next
      prop<-rule$conclusion$property;polarity<-rule$conclusion$value
      if(prop %in% names(known)) {
        if(!identical(steps[[known[[prop]]]]$fact$value,polarity))return(.inference_result("INCONSISTENT_CONTEXT",checked,NULL,list(reason="CONTRADICTORY_FACTS",property=prop)))
        next
      }
      if(length(steps)>=max_steps)return(.inference_result("UNKNOWN",checked,NULL,list(reason="BOUND_EXHAUSTED")))
      refs<-lapply(sort(names(rule$premises),method="radix"),function(p)known[[p]])
      admit(prop,polarity,"RULE",rule$id,refs);progress<-TRUE
    }
  }
  if(!property %in% names(known)||!.inference_equal(steps[[known[[property]]]]$fact,goal))
    return(.inference_result("UNKNOWN",checked,NULL,list(reason="NO_SUPPORTED_DERIVATION",
      unavailable_rules=as.list(vapply(Filter(function(r)!.inference_usable(r,checked),rules),function(r)r$id,"")))))
  witness<-list(schema_version="1.0",context=checked,catalogue_sha256=catalogue_manifest()$sha256,
                rules_sha256=resource$sha256,steps=steps,goal=known[[property]])
  check_derivation(witness,checked)
}
#' @rdname inference_context
#' @export
explain_derivation <- function(witness) {
  result<-check_derivation(witness)
  if(!identical(result$status,"ESTABLISHED")) .fail("Cannot explain an invalid or obsolete derivation")
  rules<-list_inference_rules();names(rules)<-vapply(rules,function(r)r$id,"")
  lapply(seq_along(witness$steps),function(i) {
    step<-witness$steps[[i]]
    list(step=i,fact=step$fact,premises=step$premises,explanation=if(identical(step$source,"DECLARATION"))
      "User declaration; not independently verified." else rules[[step$rule]]$argument)
  })
}

#' Search and Export the Metamathematical Catalogue
#'
#' Coverage and formal verification are separate fields. Search uses deterministic
#' ASCII case folding. Graph edges preserve their type: a dependency is not an
#' implication. The optional igraph export carries lossless canonical JSON in
#' the graph attribute \code{goedel_data} and each vertex/edge \code{record}.
#' @param query Text of at most 256 characters.
#' @param topic Optional topic identifier.
#' @param adapter Either \code{records} or the optional \code{igraph} adapter.
#' @return Topic and search lists, a typed graph record, or an igraph graph.
#' @examples
#' catalogue_topics()
#' search_catalogue("consistency")
#' catalogue_graph()
#' @export
catalogue_topics <- function() .catalogue()$topics
#' @rdname catalogue_topics
#' @export
search_catalogue <- function(query,topic=NULL) {
  if(!.scalar_string(query)||nchar(query)>256L) .fail("Search query must be text of at most 256 characters")
  if(!is.null(topic)&&(!.scalar_string(topic)||!topic %in% vapply(catalogue_topics(),function(t)t$id,""))) .fail("Unknown catalogue topic")
  fold<-function(text)chartr("ABCDEFGHIJKLMNOPQRSTUVWXYZ","abcdefghijklmnopqrstuvwxyz",text)
  needle<-fold(query);data<-.catalogue();out<-list()
  for(family in c("definitions","statements"))for(record in data[[family]]) {
    if(!is.null(topic)&&!topic %in% unlist(record$topic_ids))next
    if(grepl(needle,fold(.ascii_json(record)),fixed=TRUE)) {
      review<-if(is.null(record$evidence))record$review_status else record$evidence$review_status
      title<-if(is.null(record$title))record$name else record$title
      topics<-if(is.null(record$topic_ids))list() else record$topic_ids
      out[[length(out)+1L]]<-list(id=record$id,kind=sub("s$","",family),title=title,topic_ids=topics,review_status=review)
    }
  }
  if(length(out))out[order(vapply(out,function(r)paste(r$kind,r$id,sep=":"),""),method="radix")] else list()
}
#' @rdname catalogue_topics
#' @export
catalogue_graph <- function(adapter="records") {
  if(!.scalar_string(adapter)||!adapter %in% c("records","igraph")) .fail("Supported graph adapters are records and igraph","NOT_SUPPORTED")
  data<-.catalogue();nodes<-list();edges<-list()
  for(family in c("definitions","statements"))for(record in data[[family]]) {
    kind<-sub("s$","",family);title<-if(is.null(record$title))record$name else record$title
    topics<-if(is.null(record$topic_ids))list() else record$topic_ids
    nodes[[length(nodes)+1L]]<-list(id=paste0(kind,":",record$id),kind=kind,title=title,level="META",topic_ids=topics)
  }
  for(r in data$relations)edges[[length(edges)+1L]]<-list(id=r$id,source=paste0("statement:",r$premise),target=paste0("statement:",r$conclusion),
    kind=r$kind,requirements=r$requirements,review_status=r$evidence$review_status)
  for(rule in list_inference_rules()) {
    rid<-paste0("rule:",rule$id)
    nodes[[length(nodes)+1L]]<-list(id=rid,kind="rule",title=rule$id,level="META",topic_ids=list())
    for(prop in sort(unique(c(names(rule$premises),rule$conclusion$property)),method="radix")) {
      id<-paste0("property:",prop)
      if(!id %in% vapply(nodes,function(n)n$id,""))nodes[[length(nodes)+1L]]<-list(id=id,kind="property",title=prop,level="META",topic_ids=list())
    }
    for(prop in sort(names(rule$premises),method="radix"))edges[[length(edges)+1L]]<-list(id=paste0(rule$id,":premise:",prop),source=paste0("property:",prop),
      target=rid,kind="RULE_PREMISE",value=rule$premises[[prop]],review_status=rule$review_status)
    edges[[length(edges)+1L]]<-list(id=paste0(rule$id,":conclusion"),source=rid,target=paste0("property:",rule$conclusion$property),
      kind="RULE_CONCLUSION",value=rule$conclusion$value,review_status=rule$review_status)
  }
  graph<-list(nodes=nodes[order(vapply(nodes,function(n)n$id,""),method="radix")],
    edges=edges[order(vapply(edges,function(e)e$id,""),method="radix")],catalogue_sha256=catalogue_manifest()$sha256,rules_sha256=.inference_rules()$sha256)
  graph<-.canonical_data(graph)
  if(adapter=="records")return(graph)
  if(!requireNamespace("igraph",quietly=TRUE)) .fail("Install the optional graph dependency igraph","NOT_SUPPORTED")
  result<-igraph::make_empty_graph(n=length(graph$nodes),directed=TRUE)
  result<-igraph::set_vertex_attr(result,"name",value=vapply(graph$nodes,function(n)n$id,""))
  for(key in c("kind","title","level"))result<-igraph::set_vertex_attr(result,key,value=vapply(graph$nodes,function(n)n[[key]],""))
  result<-igraph::set_vertex_attr(result,"record",value=vapply(graph$nodes,.ascii_json,""))
  if(length(graph$edges)) {
    pairs<-unlist(lapply(graph$edges,function(e)c(e$source,e$target)),use.names=FALSE)
    result<-igraph::add_edges(result,pairs)
    for(key in c("id","kind","review_status"))result<-igraph::set_edge_attr(result,key,value=vapply(graph$edges,function(e)e[[key]],""))
    result<-igraph::set_edge_attr(result,"record",value=vapply(graph$edges,.ascii_json,""))
  }
  igraph::set_graph_attr(result,"goedel_data",.ascii_json(graph))
}
