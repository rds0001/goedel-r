# Internal validation and wire format helpers.
.fail <- function(message, code = "INVALID_INPUT") {
  stop(structure(list(message = message, call = NULL, code = code),
                 class = c("goedel_error", "error", "condition")))
}
.scalar_string <- function(x) is.character(x) && length(x) == 1L && !is.na(x)
.name_ok <- function(x) .scalar_string(x) && nchar(x, type = "bytes") <= 64L &&
  grepl("^[A-Za-z][A-Za-z0-9_]*$", x)
.term_kinds <- c("var", "const", "func", "num")
.formula_kinds <- c("pred", "eq", "not", "and", "or", "implies", "forall", "exists", "bottom")
.is_term <- function(x) x$kind %in% .term_kinds
.json_string <- function(x) as.character(jsonlite::toJSON(x, auto_unbox = TRUE))
.wire_json <- function(x) paste0('{"args":[', paste(vapply(x$args, .wire_json, ""), collapse = ","),
  '],"kind":', .json_string(x$kind), ',"name":', .json_string(x$name), '}')
.validate <- function(expr) {
  state <- new.env(parent = emptyenv()); state$n <- 0L
  arities <- new.env(parent = emptyenv())
  visit <- function(x, depth = 1L) {
    state$n <- state$n + 1L
    if (state$n > 1000L || depth > 64L) .fail("Expression resource limit exceeded", "RESOURCE_LIMIT")
    if (!is.list(x) || length(x) != 3L || is.null(names(x)) ||
        anyDuplicated(names(x)) || !setequal(names(x), c("args", "kind", "name")))
      .fail("A node must have exactly args, kind and name")
    if (!.scalar_string(x$kind) || !x$kind %in% c(.term_kinds, .formula_kinds)) .fail("Unknown node kind")
    if (!is.list(x$args) || !is.null(names(x$args))) .fail("args must be an array")
    if (!.scalar_string(x$name)) .fail("Node name must be a string")
    named <- x$kind %in% c("var", "const", "func", "pred", "forall", "exists")
    if ((named && !.name_ok(x$name)) || (!named && x$kind != "num" && x$name != "")) .fail("Invalid node name")
    if (x$kind == "num") .decimal(x$name)
    arity <- length(x$args)
    expected <- switch(x$kind, var = 0L, const = 0L, num = 0L, bottom = 0L, eq = 2L,
      not = 1L, and = 2L, or = 2L, implies = 2L, forall = 1L, exists = 1L, NULL)
    if (!is.null(expected) && arity != expected) .fail("Invalid node arity")
    if (x$kind %in% c("func", "pred")) {
      key <- paste(x$kind, x$name, sep = ":")
      if (exists(key, arities, inherits = FALSE) && get(key, arities) != arity) .fail("Inconsistent symbol arity")
      assign(key, arity, envir = arities)
    }
    for (child in x$args) {
      visit(child, depth + 1L)
      terms <- x$kind %in% c("func", "pred", "eq")
      if (terms != .is_term(child)) .fail("Term/formula position mismatch")
    }
    invisible(NULL)
  }
  visit(expr)
  if (nchar(.wire_json(expr), type = "bytes") > 65536L) .fail("Serialized expression too large", "RESOURCE_LIMIT")
  TRUE
}
.expr <- function(kind, name = "", args = list()) {
  x <- structure(list(args = args, kind = kind, name = name), class = "goedel_expr")
  .validate(x); x
}
.as_expr <- function(x) {
  structure(list(args = lapply(x$args, .as_expr), kind = x$kind, name = x$name), class = "goedel_expr")
}
.require_formula <- function(x) { .validate(x); if (.is_term(x)) .fail("Expected a formula"); invisible(x) }
.require_term <- function(x) { .validate(x); if (!.is_term(x)) .fail("Expected a term"); invisible(x) }
.sorted <- function(x) sort(unique(as.character(x)), method = "radix")

#' Construct and Validate First-Order Syntax
#'
#' Construct validated symbolic syntax, not true statements. All names are ASCII
#' identifiers beginning with a letter, of at most 64 bytes. Every expression has
#' at most 1000 nodes, depth 64 and canonical JSON size 65536 bytes. A symbol's
#' arity must be consistent within an expression. The language has no implicit
#' axioms or interpretation. Invalid inputs raise a condition of class
#' \code{goedel_error}, with \code{code} equal to \code{INVALID_INPUT} or
#' \code{RESOURCE_LIMIT}. Python has the same names except \code{exists_formula},
#' which corresponds to \code{exists}.
#' @param name A valid symbol name.
#' @param args A list of term expressions; an empty list is allowed.
#' @param left,right Expressions of the required category.
#' @param formula,body A formula expression.
#' @param variable A binder name, not a term object.
#' @param expr An expression or a wire-format node to validate.
#' @return Constructors return a validated \code{goedel_expr}. \code{validate_expr}
#' returns \code{TRUE} or raises an error. No constructor certifies truth.
#' @examples
#' x <- variable("x")
#' p <- predicate("P", list(x))
#' f <- forall("x", implication(p, p))
#' validate_expr(f)
#' equal(function_term("s", list(x)), constant("zero"))
#' negate(bottom())
#' conjunction(p, disjunction(p, exists_formula("x", p)))
#' @export
variable <- function(name) .expr("var", name)
#' @rdname variable
#' @export
constant <- function(name) .expr("const", name)
#' @rdname variable
#' @export
function_term <- function(name, args = list()) .expr("func", name, args)
#' @rdname variable
#' @export
predicate <- function(name, args = list()) .expr("pred", name, args)
#' @rdname variable
#' @export
equal <- function(left, right) .expr("eq", args = list(left, right))
#' @rdname variable
#' @export
negate <- function(formula) .expr("not", args = list(formula))
#' @rdname variable
#' @export
conjunction <- function(left, right) .expr("and", args = list(left, right))
#' @rdname variable
#' @export
disjunction <- function(left, right) .expr("or", args = list(left, right))
#' @rdname variable
#' @export
implication <- function(left, right) .expr("implies", args = list(left, right))
#' @rdname variable
#' @export
forall <- function(variable, body) .expr("forall", variable, list(body))
#' @rdname variable
#' @export
exists_formula <- function(variable, body) .expr("exists", variable, list(body))
#' @rdname variable
#' @export
bottom <- function() .expr("bottom")
#' @rdname variable
#' @export
validate_expr <- function(expr) .validate(expr)

#' @export
print.goedel_expr <- function(x, ...) {
  cat("<goedel_expr SYMBOLIC> ", serialize_record(x), "\n", sep = "")
  invisible(x)
}

.free <- function(x, bound = character()) {
  if (x$kind == "var") return(if (x$name %in% bound) character() else x$name)
  if (x$kind %in% c("forall", "exists")) bound <- c(bound, x$name)
  unlist(lapply(x$args, .free, bound = bound), use.names = FALSE)
}
.all_names <- function(x) c(x$name, unlist(lapply(x$args, .all_names), use.names = FALSE))
.rename_bound <- function(x, old, new) {
  if (x$kind == "var" && x$name == old) x$name <- new
  if (x$kind %in% c("forall", "exists") && x$name == old) return(x)
  x$args <- lapply(x$args, .rename_bound, old = old, new = new)
  x
}

#' Inspect Variables and Perform Capture-Avoiding Substitution
#'
#' Variable operations are purely syntactic. Fresh names are chosen deterministically
#' as v0, v1, and so forth. Substitution replaces only free occurrences, renaming
#' conflicting binders when necessary. Alpha normalization renames bound variables
#' in preorder, skipping free names. Alpha equality does not decide semantic
#' equivalence. Python \code{substitute} corresponds to \code{substitute_formula}.
#' @param expr A term or formula.
#' @param variable The name of the variable being replaced.
#' @param term A term to substitute.
#' @param left,right Expressions to compare modulo bound variable names.
#' @return Variable queries return sorted character vectors. Transformation
#' functions return expressions. \code{alpha_equal} returns a logical scalar.
#' @examples
#' f <- forall("y", predicate("P", list(variable("x"), variable("y"))))
#' free_variables(f)
#' bound_variables(f)
#' g <- substitute_formula(f, "x", variable("y"))
#' free_variables(g)
#' normalize(g)
#' alpha_equal(forall("x", predicate("P", list(variable("x")))),
#'             forall("z", predicate("P", list(variable("z")))))
#' @export
free_variables <- function(expr) { .validate(expr); .sorted(.free(expr)) }
#' @rdname free_variables
#' @export
bound_variables <- function(expr) {
  .validate(expr)
  walk <- function(x) c(if (x$kind %in% c("forall", "exists")) x$name else character(),
    unlist(lapply(x$args, walk), use.names = FALSE))
  .sorted(walk(expr))
}
#' @rdname free_variables
#' @export
substitute_formula <- function(expr, variable, term) {
  .validate(expr); .require_term(term)
  if (!.name_ok(variable)) .fail("Invalid substitution variable")
  forbidden <- unique(c(.all_names(expr), .all_names(term), variable))
  fresh <- function() {
    i <- 0L
    while (paste0("v", i) %in% forbidden) i <- i + 1L
    value <- paste0("v", i); forbidden <<- c(forbidden, value); value
  }
  free_term <- .free(term)
  walk <- function(x) {
    if (x$kind == "var" && x$name == variable) return(term)
    if (x$kind %in% c("forall", "exists")) {
      if (x$name == variable) return(x)
      if (x$name %in% free_term && variable %in% .free(x$args[[1L]])) {
        old <- x$name; x$name <- fresh()
        x$args[[1L]] <- .rename_bound(x$args[[1L]], old, x$name)
      }
    }
    x$args <- lapply(x$args, walk); x
  }
  result <- walk(.as_expr(expr)); .validate(result); result
}
#' @rdname free_variables
#' @export
normalize <- function(expr) {
  .validate(expr); forbidden <- .sorted(.free(expr)); counter <- 0L
  fresh <- function() {
    while (paste0("v", counter) %in% forbidden) counter <<- counter + 1L
    value <- paste0("v", counter); counter <<- counter + 1L; value
  }
  walk <- function(x, bindings = list()) {
    if (x$kind == "var" && x$name %in% names(bindings)) x$name <- bindings[[x$name]]
    if (x$kind %in% c("forall", "exists")) {
      old <- x$name; x$name <- fresh(); bindings[[old]] <- x$name
    }
    x$args <- lapply(x$args, walk, bindings = bindings); x
  }
  result <- walk(.as_expr(expr)); .validate(result); result
}
#' @rdname free_variables
#' @export
alpha_equal <- function(left, right) identical(.wire_json(normalize(left)), .wire_json(normalize(right)))

#' Canonical Syntax Serialization and Fingerprints
#'
#' Canonical JSON contains only the three node fields args, kind and name, in that
#' order, with no whitespace. Parsing accepts whitespace but rejects extra or
#' duplicated fields, invalid node categories and resource excess. It does not
#' evaluate text as R code. SHA-256 identifies canonical syntax, not semantic
#' equivalence. Python \code{serialize} corresponds to \code{serialize_record}.
#' @param expr A validated expression.
#' @param text A single JSON string, at most 65536 bytes.
#' @return Serialization and fingerprint return character scalars; deserialization
#' returns a validated expression.
#' @examples
#' x <- variable("x")
#' text <- serialize_record(x)
#' identical(serialize_record(deserialize(text)), text)
#' fingerprint(x)
#' @export
serialize_record <- function(expr) { .validate(expr); .wire_json(expr) }
#' @rdname serialize_record
#' @export
deserialize <- function(text) {
  if (!.scalar_string(text)) .fail("Expected one JSON string")
  if (nchar(text, type = "bytes") > 65536L) .fail("JSON input too large", "RESOURCE_LIMIT")
  # Bound nesting before invoking the JSON parser; quoted strings cannot contain
  # brackets in this ASCII identifier language, but count them conservatively.
  chars <- strsplit(text, "", fixed = TRUE)[[1L]]; depth <- 0L
  for (ch in chars) {
    if (ch %in% c("{", "[")) depth <- depth + 1L
    if (depth > 130L) .fail("JSON nesting too deep", "RESOURCE_LIMIT")
    if (ch %in% c("}", "]")) depth <- depth - 1L
  }
  raw <- tryCatch(jsonlite::fromJSON(text, simplifyVector = FALSE), error = function(e) .fail("Invalid JSON"))
  .validate(raw); .as_expr(raw)
}
#' @rdname serialize_record
#' @export
fingerprint <- function(expr) digest::digest(serialize_record(expr), algo = "sha256", serialize = FALSE)
