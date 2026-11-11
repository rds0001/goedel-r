.proof_json <- function(record) .fast_json(record)
#' Versioned Proof Objects and Exact Proof Transport
#'
#' Proof objects bind the native scoped calculus, numbering, theory descriptor and
#' theory hash. Construction and decoding check syntax and identity, while replay
#' checks actual inference rules. A well-formed but invalid derivation remains
#' encodable. The transport is the natural sequence [20261106,1,JSON bytes], with
#' canonical ASCII JSON. It is distinct from an arithmetical Proof_T formula and
#' makes no representability claim on its own. Resource caps remain operational.
#' @param steps Scoped proof steps.
#' @param assumptions Global trusted assumptions.
#' @param axioms Explicit trusted closed axioms.
#' @param theory Optional Q or PA presentation.
#' @param conclusion Optional required final formula.
#' @param logic Classical or intuitionistic logic.
#' @param record A proof object.
#' @param code An exact natural decimal code.
#' @param expected_theory Optional required theory identity for replay.
#' @return A proof record, exact decimal code, decoded record or native replay result.
#' @examples
#' x <- variable("x")
#' record <- proof_object(list(list(rule="eq_refl", formula=equal(x,x),
#'                                  premises=list(),scope=list())))
#' check_proof_code(encode_proof(record))$status
#' @export
proof_object <- function(steps,assumptions=list(),axioms=list(),theory=NULL,conclusion=NULL,logic="classical") {
  check_scoped_proof(steps,assumptions,axioms,theory,conclusion,logic)
  record<-list(schema_version="1.0",calculus="goedel-nd-scoped-v1",numbering="goedel-nat-sequence-v1",
    theory=theory,theory_sha256=if(is.null(theory))NULL else .data_digest(theory),assumptions=assumptions,axioms=axioms,
    conclusion=conclusion,logic=logic,steps=steps)
  jsonlite::fromJSON(.proof_json(record),simplifyVector=FALSE)
}
.proof_record <- function(record) {
  fields<-c("schema_version","calculus","numbering","theory","theory_sha256","assumptions","axioms","conclusion","logic","steps")
  if(!.fields(record,fields)||!identical(record$schema_version,"1.0")||!identical(record$calculus,"goedel-nd-scoped-v1")||!identical(record$numbering,"goedel-nat-sequence-v1")) .fail("Unknown proof envelope or identity")
  expected<-proof_object(record$steps,record$assumptions,record$axioms,record$theory,record$conclusion,record$logic)
  if(!identical(.proof_json(record),.proof_json(expected))) .fail("Mismatched proof theory identity")
  expected
}
#' @rdname proof_object
#' @export
encode_proof <- function(record) {
  bytes<-as.integer(charToRaw(.proof_json(.proof_record(record))))
  if(length(bytes)>1000000L) .fail("Proof byte budget exceeded","RESOURCE_LIMIT")
  sequence_encode(c(list("20261106","1"),as.list(as.character(bytes))))
}
#' @rdname proof_object
#' @export
decode_proof <- function(code) {
  cells<-sequence_decode(code)
  if(length(cells)<2L||cells[[1L]]!="20261106"||cells[[2L]]!="1") .fail("Unknown proof transport header")
  bytes<-cells[-c(1L,2L)]
  if(any(vapply(bytes,function(b)nchar(b)>3L||as.integer(b)>127L||as.integer(b)==0L,logical(1)))) .fail("Proof payload must contain ASCII bytes")
  text<-rawToChar(as.raw(as.integer(unlist(bytes))));chars<-strsplit(text,"",fixed=TRUE)[[1L]]
  depth<-0L;quoted<-FALSE;escaped<-FALSE
  for(ch in chars){if(escaped){escaped<-FALSE;next};if(quoted&&ch=="\\"){escaped<-TRUE;next};if(ch=='"'){quoted<-!quoted;next};if(!quoted){if(ch %in% c("{","["))depth<-depth+1L;if(depth>140L) .fail("Proof JSON depth exceeded","RESOURCE_LIMIT");if(ch %in% c("}","]"))depth<-depth-1L}}
  record<-tryCatch(jsonlite::fromJSON(text,simplifyVector=FALSE),error=function(e).fail("Malformed proof JSON"))
  record<-.proof_record(record)
  if(!identical(text,.proof_json(record))) .fail("Noncanonical proof JSON bytes")
  record
}
#' @rdname proof_object
#' @export
check_proof_code <- function(code,expected_theory=NULL) {
  record<-decode_proof(code)
  if(!is.null(expected_theory)&&!identical(.proof_json(expected_theory),.proof_json(record$theory))) .fail("Proof belongs to a different theory")
  check_scoped_proof(record$steps,record$assumptions,record$axioms,record$theory,record$conclusion,record$logic)
}
