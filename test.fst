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
let rec big_endian (b:Seq.seq U8.t) : Tot nat (decreases (FStar.Seq.length b)) =
  let open FStar.Seq in
  if length b = 0 then 0
  else
    U8.v (last b) + pow2 8 * big_endian (slice b 0 (length b - 1))

private
val big_endian_zero: len:nat -> Lemma
  (ensures (big_endian (Seq.create len 0uy) == 0))
  (decreases (len))
  [SMTPat (big_endian (Seq.create len 0uy))]
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



private
let read_length_success (b:Seq.seq U8.t{Seq.length b > 0}) : Tot bool =
  let open FStar.Seq in
  let b0 = U8.v (index b 0) in
  if b0 > 0x80 && b0 < 0x85 && length b > b0 - 0x80 then
    big_endian (slice b 1 (b0 - 0x80 + 1)) > 0
  else
    b0 < 0x80

private // Short form is easy to parse and always succeeds.
let read_length_success_lemma (b:Seq.seq U8.t{Seq.length b > 0}) : Lemma
  (requires (U8.v (Seq.index b 0) < 0x80))
  (ensures (read_length_success b))
  = ()

private // Fail when given a zero length in long form.
let read_length_success_lemma2 (b:Seq.seq U8.t{Seq.length b > 0}) : Lemma
  (requires (U8.v (Seq.index b 0) = 0x80))
  (ensures (not (read_length_success b)))
  = ()

private // We can't parse long form with more than 4 bytes.
let read_length_success_lemma3 (b:Seq.seq U8.t{Seq.length b > 0}) : Lemma
  (requires (U8.v (Seq.index b 0) > 0x84))
  (ensures (not (read_length_success b)))
  = ()

private // The long form must have enough length bytes.
let read_length_success_lemma4 (b:Seq.seq U8.t{Seq.length b > 0}) : Lemma
  (requires (U8.v (Seq.index b 0) > 0x80 /\ U8.v (Seq.index b 0) < 0x85) /\ Seq.length b <= (U8.v (Seq.index b 0)) - 0x80)
  (ensures (not (read_length_success b)))
  = ()

private // The long form must not be all zero bytes.
val read_length_success_lemma5: (b:Seq.seq U8.t{Seq.length b > 0}) -> Lemma
  (requires (U8.v (Seq.index b 0) > 0x80 /\ U8.v (Seq.index b 0) < 0x85 /\
             Seq.length b > U8.v (Seq.index b 0) - 0x80 /\
             (forall i. i > 0 /\ i < Seq.length b ==> Seq.index b i = 0uy)))
  (ensures (not (read_length_success b)))
let read_length_success_lemma5 b =
   let len = U8.v (Seq.index b 0) - 0x80 + 1 in
   assert (Seq.length b >= len /\ len >= 1);
   Seq.lemma_eq_intro (Seq.slice b 1 len) (Seq.create (len - 1) 0uy);
   assert (big_endian (Seq.create (len - 1) 0uy) = 0);
   assert (big_endian (Seq.slice b 1 len) = 0)

(* private
// Success with long form parsing means we have more than just zero bytes.
let read_length_success_lemma6 (b:Seq.seq U8.t{Seq.length b > 0}) : Lemma
  (requires (U8.v (Seq.index b 0) > 0x80 /\ U8.v (Seq.index b 0) < 0x85) /\ Seq.length b > (U8.v (Seq.index b 0)) - 0x80)
  (ensures (read_length_success b ==> big_endian (Seq.slice b 1 ((Seq.index b 0) - 0x80 + 1)) > 0 /\ b <> (Seq.create (Seq.length b) 0uy)))
  = () *)

// TODO check long form with starting zero bytes



val read_length :
  buf:buffer U8.t ->
  len:U32.t{U32.v len <= 4} ->
  ST (r:U32.t{U32.v r < pow2 (8 * U32.v len)}) // TODO
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
    //Seq.lemma_eq_intro (as_seq h lbytes) (Seq.slice (as_seq h buf) 1 (U32.v ilen + 1)); // TODO
    let hi = read_length (Buffer.sub buf 0ul len) len in
    let h = ST.get() in // TODO
    assert (U32.v hi == big_endian (Seq.slice (as_seq h buf) 0 (U32.v len))); // TODO
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


val parse_len :
  buf:buffer U8.t ->
  len:U32.t{U32.v len = length buf /\ U32.v len > 0} ->
  out_len:buffer U32.t{length out_len = 1} ->
  ST bool
  (requires (fun h -> live h buf /\ live h out_len))
  (ensures (fun h0 r h1 -> live h1 buf /\ live h1 out_len /\
            //r == read_length_success (as_seq h1 buf) /\ // TODO
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
    let tmp = read_length lbytes ilen in // TODO
    let h = ST.get() in // TODO
    assert (U32.v tmp == big_endian (Seq.slice (as_seq h buf) 1 (U32.v ilen + 1))); // TODO
    tmp // TODO
  ) in

  // Write the result.
  out_len.(0ul) <- res;

  // If we picked a result > 0, success.
  // If the result is 0 because ilen is 0, only accept the short form.
  let success = U32.(res >^ 0ul) || (ilen = 0ul && is_short_form) in

  // Short form is easy to parse and always succeeds.
  assert (U8.(b0 <^ 0x80uy) ==> res = (uint8_to_uint32 b0) /\ success);
  // TODO
  assert ((U8.(b0 >^ 0x80uy /\ b0 <^ 0x85uy) /\ (U32.v len > ((U8.v b0) - 0x80))) ==> U32.(res >=^ 0ul)); //\ success);

  let h = ST.get() in
  // Fail when given a zero length in long form.
  assert (b0 = 0x80uy ==> res = 0ul /\ not success);
  // We can't parse long form with more than 4 bytes.
  assert (U8.(b0 >^ 0x84uy) ==> res = 0ul /\ not success);
  // The long form must have enough length bytes.
  assert (U8.(b0 >^ 0x80uy /\ b0 <^ 0x85uy) /\
          (U32.v len <= (U8.v b0) - 0x80) ==> res = 0ul /\ not success);

  // TODO The long form must not be all zero bytes.
  //Seq.lemma_len_slice (as_seq h buf) 1 ((U8.v b0) - 0x80 + 1);
  //Seq.lemma_index_create ((U8.v b0) - 0x80) 0uy ((U8.v b0) - 0x80 - 1);
  assert (U8.(b0 >^ 0x80uy /\ b0 <^ 0x85uy) ==> ((U8.v b0) - 0x80) == (U32.v ilen));
  assert (U8.(b0 >^ 0x80uy /\ b0 <^ 0x85uy) ==> ((U8.v b0) - 0x80 + 1) == (U32.v ilen) + 1);
  //assert ((U8.(b0 >^ 0x80uy /\ b0 <^ 0x85uy) /\ (U32.v len > ((U8.v b0) - 0x80)) /\ (Seq.equal (Seq.slice (as_seq h buf) 1 ((U8.v b0) - 0x80 + 1)) (Seq.create ((U8.v b0) - 0x80) 0uy))) ==> res = 0ul /\ not success);
  assert (U8.(b0 >^ 0x80uy /\ b0 <^ 0x85uy) /\ (U32.v len > ((U8.v b0) - 0x80)) /\ res = 0ul ==> not success);
  assert (U8.(b0 >^ 0x80uy /\ b0 <^ 0x85uy) /\ (U32.v len > ((U8.v b0) - 0x80)) /\ not success ==> Seq.length (Seq.slice (as_seq h buf) 1 ((U8.v b0) - 0x80 + 1)) == U32.v ilen);
  assert (U8.(b0 >^ 0x80uy /\ b0 <^ 0x85uy) /\ (U32.v len > ((U8.v b0) - 0x80)) /\ not success ==> Seq.length (Seq.create ((U8.v b0) - 0x80) 0uy) == U32.v ilen);
  //assert (U8.(b0 >^ 0x80uy /\ b0 <^ 0x85uy) /\ (U32.v len > ((U8.v b0) - 0x80)) /\ not success ==> (Seq.lemma_eq_intro (Seq.slice (as_seq h buf) 1 ((U8.v b0) - 0x80 + 1)) (Seq.create ((U8.v b0) - 0x80) 0uy)));
  //assert (U8.(b0 >^ 0x80uy /\ b0 <^ 0x85uy) /\ (U32.v len > ((U8.v b0) - 0x80)) /\ not success ==> (Seq.equal (Seq.slice (as_seq h buf) 1 ((U8.v b0) - 0x80 + 1)) (Seq.create ((U8.v b0) - 0x80) 0uy)));
  //assert (b0 = 0x81uy /\ (U32.v len > ((U8.v b0) - 0x80)) /\ not success ==> get h buf 1 == 0uy);
  //assert (b0 = 0x82uy /\ (U32.v len > ((U8.v b0) - 0x80)) /\ not success ==> get h buf 1 == 0uy /\ get h buf 2 == 0uy);
  //assert (b0 = 0x83uy /\ (U32.v len > ((U8.v b0) - 0x80)) /\ not success ==> get h buf 1 == 0uy /\ get h buf 2 == 0uy /\ get h buf 3 == 0uy);
  //assert (b0 = 0x84uy /\ (U32.v len > ((U8.v b0) - 0x80)) /\ not success ==> get h buf 1 == 0uy /\ get h buf 2 == 0uy /\ get h buf 3 == 0uy /\ get h buf 4 == 0uy);
  // TODO
  //assert (b0 = 0x81uy /\ (U32.v len > ((U8.v b0) - 0x80)) /\ not success ==> Seq.equal (Seq.slice (as_seq h buf) 1 2) (Seq.create 1 0uy));
  //assert (b0 = 0x81uy /\ (U32.v len > ((U8.v b0) - 0x80)) /\ not success ==> Seq.equal (Seq.slice (as_seq h buf) 1 2) (Seq.create ((U8.v b0) - 0x80) 0uy));
  //assert (b0 = 0x81uy /\ (U32.v len > ((U8.v b0) - 0x80)) /\ not success ==> Seq.equal (Seq.slice (as_seq h buf) ((U8.v b0) - 0x80) 2) (Seq.create ((U8.v b0) - 0x80) 0uy));
  //assert (b0 = 0x81uy /\ (U32.v len > ((U8.v b0) - 0x80)) /\ not success ==> Seq.equal (Seq.slice (as_seq h buf) ((U8.v b0) - 0x80) ((U8.v b0) - 0x80 + 1)) (Seq.create ((U8.v b0) - 0x80) 0uy));
  //assert (U8.v b0 > 081 /\ (U32.v len > ((U8.v b0) - 0x80)) /\ not success ==> Seq.equal (Seq.slice (as_seq h buf) ((U8.v b0) - 0x80) ((U8.v b0) - 0x80 + 1)) (Seq.create ((U8.v b0) - 0x80) 0uy));

  // TODO check long form with starting zero bytes

  success
