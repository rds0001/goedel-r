#' Exact Natural-Number Coding of Syntax
#'
#' The versioned numbering starts at one and, for each byte b of canonical UTF-8
#' JSON, replaces n by 256*n+b. The leading one is a sentinel. The encoding is
#' injective because the base-256 expansion recovers every byte; it is a concrete
#' syntax numbering, not an arithmetized proof of representability. Native R
#' decimal-digit arithmetic avoids rounding through doubles. The maximum encoded
#' size is 1024 bytes and codes contain at most 2500 decimal digits. Decoding
#' rejects noncanonical JSON, invalid codes, missing sentinels and oversized input.
#' @param expr A validated expression.
#' @param code A positive canonical decimal string, with no leading zero.
#' @return \code{encode} returns a decimal character scalar; \code{decode} returns
#' an expression. \code{numbering} returns metadata describing the convention.
#' @examples
#' code <- encode(variable("x"))
#' code
#' alpha_equal(decode(code), variable("x"))
#' numbering()
#' @export
encode <- function(expr) {
  bytes <- as.integer(charToRaw(serialize_record(expr)))
  if (length(bytes) > 1024L) .fail("Encoded expression exceeds 1024 bytes", "RESOURCE_LIMIT")
  digits <- 1L # little-endian decimal digits; all arithmetic intermediates <2560.
  for (b in bytes) {
    carry <- b
    for (i in seq_along(digits)) {
      value <- digits[[i]] * 256L + carry
      digits[[i]] <- value %% 10L; carry <- value %/% 10L
    }
    while (carry > 0L) { digits <- c(digits, carry %% 10L); carry <- carry %/% 10L }
  }
  paste(rev(digits), collapse = "")
}
#' @rdname encode
#' @export
decode <- function(code) {
  if (!.scalar_string(code)) .fail("Code must be a decimal string")
  if (nchar(code, type = "bytes") > 2500L) .fail("Code exceeds 2500 digits", "RESOURCE_LIMIT")
  if (!grepl("^[1-9][0-9]*$", code)) .fail("Noncanonical decimal code")
  digits <- utf8ToInt(code) - 48L; bytes <- integer()
  while (!(length(digits) == 1L && digits[[1L]] == 1L)) {
    carry <- 0L; quotient <- integer(length(digits))
    for (i in seq_along(digits)) {
      value <- carry * 10L + digits[[i]]
      quotient[[i]] <- value %/% 256L; carry <- value %% 256L
    }
    bytes <- c(bytes, carry)
    if (length(bytes) > 1024L) .fail("Decoded expression exceeds 1024 bytes", "RESOURCE_LIMIT")
    first <- which(quotient != 0L)
    if (!length(first)) .fail("Missing encoding sentinel")
    digits <- quotient[seq.int(first[[1L]], length(quotient))]
  }
  if (!length(bytes) || any(bytes == 0L)) .fail("Code contains no valid canonical JSON")
  text <- tryCatch(rawToChar(as.raw(rev(bytes))), error = function(e) .fail("Invalid encoded bytes"))
  if (is.na(iconv(text, from = "UTF-8", to = "UTF-8"))) .fail("Invalid UTF-8")
  expr <- deserialize(text)
  if (!identical(text, serialize_record(expr))) .fail("Encoded JSON is not canonical")
  expr
}
#' @rdname encode
#' @export
numbering <- function() list(id = "goedel-json-byte-v1", version = "1.0", max_bytes = 1024L,
  description = "Sentinel-prefixed base-256 canonical JSON bytes; exact decimal string.")
