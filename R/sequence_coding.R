#' Exact Self-Delimiting Natural-Number Sequences
#'
#' The numbering goedel-nat-sequence-v1 has empty code 1. For a head a, let
#' v=a+1, k be its binary length and p=v-2^(k-1). The cell is
#' (tail * 2^(2*k)) + (2^k-1) + 2^(k+1)*p. Reading from the least significant
#' end gives k ones, a zero, and k-1 payload bits. Code zero is invalid. Exact GMP
#' integers are used internally; public numbers remain canonical decimal strings.
#' These finite coding operations do not assert arithmetical representability.
#' @param values An unnamed list or character vector of natural decimal strings.
#' @param code A canonical positive decimal string.
#' @param max_items Maximum sequence length, an integer in 0 through 1000000.
#' @param max_bits Maximum encoded binary length, in 1 through 16000000.
#' @return Encoding returns a decimal string; decoding returns a list of decimal strings.
#' @examples
#' sequence_encode(list("0")) # "5"
#' sequence_decode(sequence_encode(list("0","1","12345678901234567890")))
#' @export
sequence_encode <- function(values,max_items=1000000L,max_bits=16000000L) {
  if(!.register_integer(max_items,0L,1000000L)) .fail("Invalid max_items budget")
  .int_budget(max_bits,16000000L,"max_bits")
  if(is.character(values))values<-as.list(values);.array(values,"values")
  if(length(values)>max_items) .fail("Sequence item budget exceeded","RESOURCE_LIMIT")
  blocks<-vector("list",length(values));size<-1L;cache<-new.env(hash=TRUE,parent=emptyenv())
  for(i in seq_along(values)) {
    value<-values[[i]]
    if(.scalar_string(value)&&nzchar(value)&&nchar(value)<=64L&&exists(value,envir=cache,inherits=FALSE))block<-get(value,envir=cache,inherits=FALSE) else {
      n<-.big_nat(value,5000000L);binary<-as.character(n+1L,b=2);k<-nchar(binary)
      if(2L*k+size>max_bits) .fail("Sequence bit budget exceeded","RESOURCE_LIMIT")
      block<-paste0(substring(binary,2L),"0",strrep("1",k));if(nchar(value)<=64L)assign(value,block,envir=cache)
    }
    size<-size+nchar(block);if(size>max_bits) .fail("Sequence bit budget exceeded","RESOURCE_LIMIT")
    blocks[[i]]<-block
  }
  as.character(gmp::as.bigz(paste0("0b1",paste(rev(blocks),collapse=""))))
}
#' @rdname sequence_encode
#' @export
sequence_decode <- function(code,max_items=1000000L,max_bits=16000000L) {
  if(!.register_integer(max_items,0L,1000000L)) .fail("Invalid max_items budget")
  .int_budget(max_bits,16000000L,"max_bits")
  n<-.big_nat(code,5000000L);if(n==0L) .fail("Zero is not a sequence code")
  bits<-as.character(n,b=2);cursor<-nchar(bits);if(cursor>max_bits) .fail("Sequence bit budget exceeded","RESOURCE_LIMIT")
  zeroes<-gregexpr("0",bits,fixed=TRUE)[[1L]];zeroes<-zeroes[zeroes>0L];previous_zero<-integer(cursor);previous_zero[zeroes]<-zeroes;previous_zero<-cummax(previous_zero);out<-list()
  while(cursor>1L) {
    if(length(out)>=max_items) .fail("Sequence item budget exceeded","RESOURCE_LIMIT")
    z<-previous_zero[[cursor]];if(z==0L) .fail("Missing cell delimiter")
    k<-cursor-z
    if(k<1L||cursor-2L*k<1L) .fail("Invalid self-delimiting sequence cell")
    payload<-if(k==1L)"" else substring(bits,z-k+1L,z-1L)
    out[[length(out)+1L]]<-as.character(gmp::as.bigz(paste0("0b1",payload))-1L)
    cursor<-cursor-2L*k
  };out
}
.dag_tags <- c("num","var","zero","succ","add","mul","eq","not","and","or","implies","forall","exists","bottom")
#' Encode Arithmetic DAGs and Perform Closed Numeral Substitution
#'
#' The DAG sequence starts with magic 20261105, version 1 and the node count.
#' Each node has four natural cells: tag, numeric name, left child and right child.
#' Unused fields are zero; the root is always the last node.
#' Numeric children are one-based, with zero denoting absence. Tags are num, var,
#' zero, succ, add, mul, eq, not, and, or, implies, forall,
#' exists, bottom, numbered from zero. Envelope indices are zero-based and backward.
#' Closed numeral substitution preserves the original node prefix, then appends
#' one transformed copy per node. A binder for the replaced variable retains its
#' original body. This convention is shared with the concrete substitution program.
#' Invalid mathematical codes totalize to zero in substitute_code; explicit
#' resource exhaustion remains an error, never the mathematical value zero.
#' @param dag A term or formula DAG in the numbered arithmetic profile.
#' @param code A natural decimal string containing a DAG code.
#' @param variable An indexed DAG variable name xN.
#' @param variable_index The canonical decimal index N.
#' @param value A canonical decimal numeral value.
#' @return Encoding and code substitution return decimal strings; decoding and
#' symbolic substitution return arithmetic DAGs.
#' @examples
#' d <- arithmetic_dag(parse_formula("x = x"))
#' code <- arithmetic_dag_encode(d)
#' identical(arithmetic_dag_decode(code), d)
#' @export
arithmetic_dag_encode <- function(dag) {
  .dag_info(dag,TRUE)
  if(dag$root!=length(dag$nodes)-1L) .fail("Numbered DAG root must be last")
  cells<-vector("list",4L*length(dag$nodes)+3L);cells[1:3]<-list("20261105","1",as.character(length(dag$nodes)));position<-4L
  for(nd in dag$nodes) {
    tag<-match(nd$op,.dag_tags)-1L;if(is.na(tag)) .fail("DAG operation outside numbered profile")
    name<-if(nd$op=="num")nd$name else if(nd$op %in% c("var","forall","exists"))substring(nd$name,2L) else "0"
    left<-if(length(nd$args))as.character(as.integer(nd$args[[1L]])+1L) else "0"
    right<-if(length(nd$args)==2L)as.character(as.integer(nd$args[[2L]])+1L) else "0"
    cells[seq.int(position,position+3L)]<-list(as.character(tag),name,left,right);position<-position+4L
  }
  sequence_encode(cells)
}
#' @rdname arithmetic_dag_encode
#' @export
arithmetic_dag_decode <- function(code) {
  cells<-sequence_decode(code);if(length(cells)<7L||cells[[1L]]!="20261105"||cells[[2L]]!="1") .fail("Unknown DAG numbering envelope")
  nbig<-.big_nat(cells[[3L]]);if(nbig<1L) .fail("Empty numbered DAG")
  if(nbig>200000L) .fail("DAG node budget exceeded","RESOURCE_LIMIT")
  n<-as.integer(nbig);if(length(cells)!=4L*n+3L) .fail("Invalid numbered DAG length/root")
  nodes<-vector("list",n);arity<-c(0L,0L,0L,1L,2L,2L,2L,1L,2L,2L,2L,1L,1L,0L)
  for(i in seq_len(n)) {
    row<-cells[seq.int(4L*i,4L*i+3L)];tagbig<-.big_nat(row[[1L]])
    if(tagbig>13L) .fail("Unknown arithmetic node tag")
    tag<-as.integer(tagbig);op<-.dag_tags[[tag+1L]];a<-arity[[tag+1L]]
    if((!op %in% c("num","var","forall","exists")&&row[[2L]]!="0")||(a<1L&&row[[3L]]!="0")||(a<2L&&row[[4L]]!="0")) .fail("Nonzero unused DAG field")
    args<-list()
    if(a>0L)for(j in seq_len(a)){v<-.big_nat(row[[j+2L]]);if(v<1L||v>=i) .fail("Nonbackward DAG reference");args[[j]]<-as.integer(v)-1L}
    name<-if(op=="num")row[[2L]] else if(op %in% c("var","forall","exists"))paste0("x",row[[2L]]) else ""
    nodes[[i]]<-list(op=op,name=name,args=args)
  }
  out<-list(schema_version="1.0",nodes=nodes,root=n-1L);.dag_info(out,TRUE);out
}
#' @rdname arithmetic_dag_encode
#' @export
dag_substitute_numeral <- function(dag,variable,value) {
  .dag_info(dag,FALSE);if(!.dag_name(variable)) .fail("Expected indexed variable")
  .big_nat(value,5000000L);n<-length(dag$nodes)
  if(2L*n>200000L) .fail("Substituted DAG node budget exceeded","RESOURCE_LIMIT")
  transformed<-lapply(dag$nodes,function(nd) {
    if(nd$op=="var"&&nd$name==variable)return(list(op="num",name=value,args=list()))
    if(!nd$op %in% c("forall","exists")||nd$name!=variable)nd$args<-lapply(nd$args,function(a)a+n)
    nd
  })
  out<-list(schema_version="1.0",nodes=c(dag$nodes,transformed),root=dag$root+n);.dag_info(out,FALSE);out
}
#' @rdname arithmetic_dag_encode
#' @export
substitute_code <- function(code,variable_index,value) {
  .big_nat(code,5000000L);.big_nat(variable_index,4096L);.big_nat(value,5000000L)
  tryCatch(arithmetic_dag_encode(dag_substitute_numeral(arithmetic_dag_decode(code),paste0("x",variable_index),value)),
    goedel_error=function(e){if(e$code=="RESOURCE_LIMIT")stop(e);"0"})
}
