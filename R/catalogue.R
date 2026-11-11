.catalogue <- function() {
  path <- system.file("extdata", "catalogue.json", package = "goedel")
  if (!nzchar(path)) .fail("Catalogue resource unavailable")
  jsonlite::fromJSON(path, simplifyVector = FALSE)
}
.lookup <- function(id, family) {
  if (!.scalar_string(id)) .fail("ID must be one string")
  rows <- .catalogue()[[family]]
  match <- Filter(function(x) identical(x$id, id), rows)
  if (length(match) != 1L) .fail(paste("Unknown", family, "ID"))
  match[[1L]]
}
.validate_context <- function(context) {
  if (!is.list(context) || length(context) != 3L || anyDuplicated(names(context)) ||
      !setequal(names(context), c("id", "assumptions", "consistency_status")) ||
      !.scalar_string(context$id) || !nzchar(context$id) || nchar(context$id, type = "chars") > 128L || !.scalar_string(context$consistency_status) || context$consistency_status != "NOT_ESTABLISHED") .fail("Invalid theory context")
  a <- context$assumptions
  if (is.list(a) && length(a) > 1000L) .fail("Too many assumption declarations", "RESOURCE_LIMIT")
  if (!is.list(a) || (length(a) > 0L && (is.null(names(a)) || anyDuplicated(names(a)) || anyNA(names(a)) || any(!nzchar(names(a)))))) .fail("Assumptions must be a named list")
  if (any(!vapply(a, function(x) is.logical(x) && length(x) == 1L && !is.na(x), logical(1)))) .fail("Assumptions must be boolean declarations")
  TRUE
}

#' Declare a Theory Context Without Certifying It
#'
#' Context assumptions are user declarations, not verified properties. No hidden
#' inference follows from a theory name. In particular consistency_status always
#' remains NOT_ESTABLISHED. The context is used only for conditional catalogue
#' applicability, not as an implicit axiom source for proof checking.
#' @param name A nonempty theory label, at most 128 Unicode characters.
#' @param assumptions A named list of logical scalars, without missing values.
#' @return A \code{goedel_context} containing id, assumptions and consistency_status.
#' @examples
#' theory_context("PA", list(consistent = TRUE, effective_axiomatized = TRUE))
#' @export
theory_context <- function(name, assumptions = list()) {
  if (is.list(assumptions) && length(assumptions) == 0L) assumptions <- .empty_object()
  x <- structure(list(id = name, assumptions = assumptions, consistency_status = "NOT_ESTABLISHED"), class = "goedel_context")
  .validate_context(x); x
}

#' Query Versioned Mathematical Definitions and Statements
#'
#' Catalogue entries are independently phrased literature records with their
#' hypotheses, sources, review status and limitations. They are not formal proofs.
#' Lists return sorted IDs; lookup of an unknown ID raises INVALID_INPUT.
#' The manifest hashes the exact installed canonical source bytes. The graph
#' contains only documented direct typed edges and supports no transitive theorem
#' inference. Function names correspond directly to Python.
#' @param id A catalogue identifier.
#' @return ID queries return character vectors, lookups return lists, and the
#' graph and manifest return named lists.
#' @examples
#' ids <- list_statements()
#' if (length(ids)) lookup_statement(ids[[1L]])$title
#' definitions <- list_definitions()
#' if (length(definitions)) definition(definitions[[1L]])
#' relation_graph()
#' catalogue_manifest()
#' @export
list_statements <- function() .sorted(vapply(.catalogue()$statements, function(x) x$id, ""))
#' @rdname list_statements
#' @export
lookup_statement <- function(id) .lookup(id, "statements")
#' @rdname list_statements
#' @export
list_definitions <- function() .sorted(vapply(.catalogue()$definitions, function(x) x$id, ""))
#' @rdname list_statements
#' @export
definition <- function(id) .lookup(id, "definitions")
#' @rdname list_statements
#' @export
relation_graph <- function() {
  cat <- .catalogue()
  list(nodes = as.list(.sorted(vapply(cat$statements, function(x) x$id, ""))), edges = cat$relations[order(vapply(cat$relations, function(x) x$id, ""), method = "radix")])
}
#' @rdname list_statements
#' @export
catalogue_manifest <- function() {
  cat <- .catalogue(); path <- system.file("extdata", "catalogue.json", package = "goedel")
  list(schema_version = cat$schema_version, catalogue_version = cat$catalogue_version, sha256 = digest::digest(file = path, algo = "sha256", serialize = FALSE))
}

#' Check Conditional Applicability of a Literature Statement
#'
#' A matching theory label does not establish any hypothesis. Missing requirements
#' produce UNKNOWN, explicitly false requirements produce NOT_APPLICABLE, and
#' unreviewed evidence remains UNKNOWN. ESTABLISHED means conditional applicability
#' under declared assumptions. It never certifies those assumptions or consistency.
#' A detected contradiction between consistent=FALSE and omega_consistent=TRUE
#' or sigma1_sound=TRUE takes precedence and yields INCONSISTENT_CONTEXT.
#' @param id A statement identifier.
#' @param context A context made by \code{theory_context}.
#' @return A \code{goedel_result} with missing/violated requirements in details,
#' source evidence and explicit trust limitations. No formal proof is produced.
#' @examples
#' ids <- list_statements()
#' if (length(ids)) check_applicability(ids[[1L]], theory_context("unspecified"))$status
#' @export
check_applicability <- function(id, context) {
  statement <- lookup_statement(id); .validate_context(context)
  a <- context$assumptions
  required <- .sorted(unlist(statement$requirements, use.names = FALSE))
  missing <- .sorted(setdiff(required, names(a)))
  violated <- .sorted(required[vapply(required, function(k) !is.null(a[[k]]) && identical(a[[k]], FALSE), logical(1))])
  inconsistent <- identical(a[["consistent"]], FALSE) && (identical(a[["omega_consistent"]], TRUE) || identical(a[["sigma1_sound"]], TRUE))
  e <- statement$evidence
  reviewed <- identical(e$kind, "LITERATURE_RESULT") && identical(e$review_status, "REVIEWED") && e$verification_status %in% c("INDEPENDENTLY_CHECKED", "FORMALLY_VERIFIED")
  status <- if (inconsistent) "INCONSISTENT_CONTEXT" else if (!reviewed) "UNKNOWN" else if (length(violated)) "NOT_APPLICABLE" else if (length(missing)) "UNKNOWN" else "ESTABLISHED"
  .result(status, "CATALOGUE", id, assumptions = a, evidence = list(e),
    limitations = c(unlist(statement$limitations, use.names = FALSE), "Applicability is conditional on declarations; assumptions are not verified."),
    context = context, dependencies = as.list(required), details = list(missing_requirements = as.list(missing), violated_requirements = as.list(violated)))
}
