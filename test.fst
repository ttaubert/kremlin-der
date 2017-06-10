module Test

open FStar
open FStar.ST
open FStar.Mul
open FStar.UInt
open FStar.Buffer
open FStar.Int.Cast

module U8 = FStar.UInt8
module U32 = FStar.UInt32

#reset-options "--initial_fuel 1 --max_fuel 1"


val read_length :
  buf:buffer U8.t ->
  len:U32.t{U32.v len < 5} ->
  Stack (r:U32.t{U32.v r < pow2 (8 * U32.v len)})
  (requires (fun h -> live h buf /\ U32.v len == length buf))
  (ensures (fun h0 _ h1 -> h0 == h1 /\ live h1 buf))
  (decreases (length buf))

let rec read_length buf len =
  if len = 0ul then 0ul
  else (
    let open U32 in
    let len = len -^ 1ul in
    let bi = index buf len in
    let lo = uint8_to_uint32 bi in
    Math.Lemmas.pow2_plus 8 24;
    let hi = read_length (Buffer.sub buf 0ul len) len in
    assert (U32.v hi < pow2 (8 * (U32.v len)));
    let hi' = hi <<^ 8ul in
    let res = hi' |^ lo in
    UInt.logor_disjoint #32 (v hi') (v lo) 8;
    assert (v res == pow2 8 * (v hi) + (v lo));
    res
  )


val parse_len :
  buf:buffer U8.t ->
  len:U32.t{U32.v len = length buf /\ U32.v len > 0} ->
  out_len:buffer U32.t{length out_len = 1} ->
  Stack bool
  (requires (fun h -> live h buf /\ live h out_len /\ (get h out_len 0) = 0ul))
  (ensures (fun h0 r h1 -> live h1 buf /\ live h1 out_len /\ (r \/ (get h1 out_len 0) = 0ul)))

let parse_len buf len out_len =
  let b0 = index buf 0ul in
  // Length bits.
  let ilen = U8.(b0 &^ 127uy) in
  UInt.logand_mask (U8.v b0) 7;
  assert (U8.v ilen < 128);
  // Length form.
  let is_short_form = (b0 = ilen) in
  assert (is_short_form ==> not (nth (U8.v b0) 0));
  let ilen = uint8_to_uint32 ilen in

  // Handle short form first.
  let res = if is_short_form then
    ilen
  // Accept 4 bytes max. for long form.
  else if U32.(ilen >^ 4ul) then
    0ul
  // Check that we have enough bytes.
  else if U32.(len <=^ ilen) then
    0ul
  // Reject long form with zero bytes.
  else if ilen = 0ul then
    0ul
  // Parse long form.
  else (
    assert (not is_short_form);
    assert (length buf > U32.v ilen);
    assert (U32.v ilen > 0 && U32.v ilen < 5);
    read_length (Buffer.sub buf 1ul ilen) ilen
  ) in

  out_len.(0ul) <- res;
  // If we picked a result > 0, success.
  // If the result is 0 because ilen is 0, only accept the short form.
  U32.(res >^ 0ul) || (ilen = 0ul && is_short_form)

// TODO tests
