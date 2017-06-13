module Test

open FStar
open FStar.Buffer
open FStar.Int.Cast
open FStar.Mul

module U8 = FStar.UInt8
module U32 = FStar.UInt32

//#reset-options "--initial_fuel 1 --max_fuel 1"
#reset-options "--max_fuel 1 --z3rlimit 100"


private (* HACL* -> FStar.Endianness *)
let rec big_endian (b:FStar.Seq.seq U8.t) : Tot nat (decreases (FStar.Seq.length b)) =
  let open FStar.Seq in
  if length b = 0 then 0
  else
    U8.v (last b) + pow2 8 * big_endian (slice b 0 (length b - 1))

private
val big_endian_zero: len:nat{len <= 4} -> Lemma
  (ensures (big_endian (Seq.create len 0uy) == 0))
  (decreases (len))
let rec big_endian_zero len =
  let open FStar.Seq in
  if len = 0 then ()
  else (
    let nlen = len - 1 in
    lemma_eq_intro (slice (create len 0uy) 0 nlen) (create nlen 0uy);
    //assert (big_endian (create len 0uy) == 0 + pow2 8 * big_endian (slice (create len 0uy) 0 (len - 1)));
    big_endian_zero nlen
  )

private
val big_endian_single: n:U8.t -> Lemma
  (ensures (big_endian (Seq.create 1 n) == U8.v n))
let big_endian_single n =
  let open FStar.Seq in
  let s = (create 1 n) in
  assert (big_endian s == U8.v (index s 0) + pow2 8 * big_endian (slice s 0 0))




val read_length :
  buf:buffer U8.t ->
  len:U32.t{U32.v len <= 4} ->
  ST (r:U32.t{U32.v r < pow2 (8 * U32.v len)})
  (requires (fun h -> live h buf /\ U32.v len == length buf))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live h1 buf /\ U32.v r == big_endian (as_seq h0 buf)))
  (decreases (length buf))

let rec read_length buf len =
  if len = 0ul then 0ul
  else (
    let open U32 in
    let len = len -^ 1ul in
    let bi = index buf len in
    let lo = uint8_to_uint32 bi in
    Math.Lemmas.pow2_plus 8 24;
    // TODO assert Buffer.sub
    let hi = read_length (Buffer.sub buf 0ul len) len in
    assert (U32.v hi < pow2 (8 * (U32.v len)));
    let hi' = hi <<^ 8ul in
    assert (hi = 0ul ==> hi' = 0ul);
    let res = hi' |^ lo in
    UInt.logor_disjoint #32 (v hi') (v lo) 8;
    assert (v res == pow2 8 * (v hi) + (v lo));
    assert (hi' = 0ul ==> res = lo);
    assert (lo = 0ul ==> res = hi');
    assert (hi' = 0ul /\ lo = 0ul ==> res = 0ul);
    res
  )

(*
private // TODO len <= 4
val test_parse_long_zero : len:U32.t{U32.v len < 2} -> St unit

let rec test_parse_long_zero len = match (U32.v len) with
  | 0 -> ()
  | 1 -> (
      push_frame ();
      let sdata = Seq.create (U32.v len - 1) 0uy in
      //let data = create 0uy U32.(len -^ 1ul) in
      let data = of_seq sdata U32.(len -^ 1ul) in
      assert (length data = 0);
      assert (read_length data 0ul = 0ul);
      //Seq.lemma_index_create (U32.v len - 1) 0uy (U32.v len - 2);
      let h = ST.get() in
      Seq.lemma_eq_intro (as_seq h data) (Seq.create (U32.v len - 1) 0uy);
      assert (read_length data U32.(len -^ 1ul) = 0ul);
      pop_frame ()

      //push_frame ();
      //test_parse_long_zero U32.(len -^ 1ul);
      //let data = create 0uy len in
      //let h = ST.get() in
      //Seq.lemma_eq_intro (as_seq h data) (Seq.create (U32.v len) 0uy);
      //assert (read_length data len = 0ul);
      //pop_frame ()
    )
  *)

  //push_frame ();
  //let data = create 0uy len in
  //let h = ST.get() in
  //Seq.lemma_index_create 1 0x80uy 0;
  //Seq.lemma_eq_intro (as_seq h data) (Seq.create (U32.v len) 0uy);
  //assert (get h data 0 = 0uy);
  //let out_len = create 1ul 1ul in
  //Seq.lemma_index_create 1 0ul (U32.v len);
  //let h = ST.get() in
  //Seq.lemma_eq_intro (as_seq h out_len) (Seq.create 1 1ul);
  //assert (read_length data len = 0ul);
  //let h = ST.get() in
  //assert (not success && get h out_len 0 = 0ul);
  //assert (get h out_len 0 = 0ul);
  //Seq.lemma_eq_intro (as_seq h out_len) (Seq.create 1 0ul);
  //pop_frame ()


val parse_len :
  buf:buffer U8.t ->
  len:U32.t{U32.v len = length buf /\ U32.v len > 0} ->
  out_len:buffer U32.t{length out_len = 1} ->
  ST bool
  (requires (fun h -> live h buf /\ live h out_len))
  (ensures (fun h0 r h1 -> live h1 buf /\ live h1 out_len /\
            (r \/ (get h1 out_len 0) = 0ul)))

let parse_len buf len out_len =
  let b0 = index buf 0ul in
  // Length bits.
  let ilen = U8.(b0 &^ 0x7fuy) in
  UInt.logand_mask (U8.v b0) 7;
  assert (U8.v ilen < 0x80);
  // Length form.
  let is_short_form = (b0 = ilen) in
  assert (is_short_form ==> not (UInt.nth (U8.v b0) 0));
  let ilen = uint8_to_uint32 ilen in

  // Handle short form first.
  let res = if is_short_form then
    ilen
  // Reject long form with zero bytes.
  else if U32.(ilen =^ 0ul) then
    0ul
  // Accept 4 bytes max. for long form.
  else if U32.(ilen >^ 4ul) then
    0ul
  // Check that we have enough bytes.
  else if U32.(len <=^ ilen) then
    0ul
  // Parse long form.
  else (
    assert (not is_short_form);
    assert (length buf > U32.v ilen);
    assert (U32.v ilen > 0 && U32.v ilen < 5);
    let lbytes = Buffer.sub buf 1ul ilen in
    let h = ST.get() in // TODO
    Seq.lemma_eq_intro (as_seq h lbytes) (Seq.slice (as_seq h buf) 1 (U32.v ilen + 1));
    read_length lbytes ilen
  ) in

  // Write the result. (TODO write without temp var?)
  out_len.(0ul) <- res;

  // If we picked a result > 0, success.
  // If the result is 0 because ilen is 0, only accept the short form.
  let success = U32.(res >^ 0ul) || (ilen = 0ul && is_short_form) in

  // Short form is easy to parse.
  assert (U8.(b0 <^ 0x80uy) ==> res = (uint8_to_uint32 b0) /\ success);
  // TODO
  //assert (U8.(b0 >^ 0x80uy /\ b0 <^ 0x85uy) /\
          //(U32.v len > (U8.v b0) - 0x80) ==> U32.(res >=^ 0ul) /\ success);

  let h = ST.get() in
  // Fail when given a zero length in long form.
  assert (b0 = 0x80uy ==> res = 0ul /\ not success);
  // We can't parse long form with more than 4 bytes.
  assert (U8.(b0 >^ 0x84uy) ==> res = 0ul /\ not success);
  // The long form must have enough length bytes.
  assert (U8.(b0 >^ 0x80uy /\ b0 <^ 0x85uy) /\
          (U32.v len <= (U8.v b0) - 0x80) ==> res = 0ul /\ not success);
  // The long form must not be all zero bytes. TODO
  //Seq.lemma_len_slice (as_seq h buf) 1 ((U8.v b0) - 0x80 + 1);
  //Seq.lemma_index_create ((U8.v b0) - 0x80) 0uy ((U8.v b0) - 0x80 - 1);
  //assert (U8.(b0 >^ 0x80uy /\ b0 <^ 0x85uy) /\
          //(U32.v len > (U8.v b0) - 0x80) /\
          //(Seq.equal (Seq.slice (as_seq h buf) 1 ((U8.v b0) - 0x80 + 1)) (Seq.create ((U8.v b0) - 0x80) 0uy)) ==> res = 0ul /\ not success);

  // TODO check long form with starting zero bytes

  success
