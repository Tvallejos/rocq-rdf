From Equations Require Import Equations.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
(* Unset Strict Implicit. *)
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term Util IsoCan.

(******************************************************************************)
(*                                                                            *)
(*            template defined with equations                                 *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory.

Open Scope order_scope.

Section HashMapsAndPartitions.

  Variable B : eqType.

  (* Hash maps as sequences of pairs of a b-node and a hash *)
  Definition hash_map := seq (B * nat).

  (* Type of an element of a partition *)
  Definition part := seq (B * nat).
  (* Type of partitions *)
  Definition partition := seq part.

  (* TODO : remove *)
  Definition pred_eq {T : eqType} (t: T):= pred1 t.
  (* Tests whether the hash of p is n *)
  Definition eq_hash (n : nat) (p: B * nat) := pred1 n p.2.
  (* Tests whether the node of p is b *)
  Definition eq_bnode (b : B) (p: B * nat) := pred1 b p.1.

  (* the hashes of a hashmap *)
  Definition hashes_hm (hm : hash_map): seq nat :=
    map snd hm.
  
  (* splits hm according to hash n *)
  Definition partitionate (n : nat) (hm : hash_map) :=
    (filter (eq_hash n) hm, filter (negb \o eq_hash n) hm).

  Definition part_of (hm : hash_map) (n : nat) :=
    filter (eq_hash n) hm.

  Definition gen_partition (hm : hash_map) : partition :=
    map (part_of hm) (undup (hashes_hm hm)).

  (* Equations? gen_partition (hm : hash_map) : partition by wf (size hm) lt :=
    gen_partition nil := nil;
    gen_partition (bn::l) :=
      ((partitionate bn.2 (bn::l)).1) :: gen_partition (partitionate bn.2 (bn::l)).2.
  Proof.
  rewrite /= /eq_hash/pred_eq/negb /= eqxx /=.
  have H := size_filter_le ((fun b : bool => if b then false else true) \o (fun p : B * nat => n == p.2)) l.
  by apply /ssrnat.ltP; apply : leq_trans H _.
  Qed.
 *)
  Lemma hm_zip (hm : hash_map): hm = zip (map fst hm) (map snd hm).
  Proof. by rewrite zip_map; elim: hm => [//| [h1 h2] tl IHtl] /=; rewrite -IHtl. Qed.

  Lemma eq_hash_refl (bn : (B * nat)) : eq_hash bn.2 bn.
  Proof. by rewrite /eq_hash /pred_eq /pred1 /= eqxx. Qed.

  Lemma eq_hash_sym (bn1 bn2 : (B * nat)) : eq_hash bn1.2 bn2 = eq_hash bn2.2 bn1.
  Proof. 
  by apply /idP/idP; rewrite /eq_hash/pred_eq /pred1 => /eqP-> /=.
  Qed.

  Lemma part_size (hm : hash_map) (p : part) :
     p \in (gen_partition hm) -> (size p > 0)%N.
  Proof.
  case/mapP=> /= n hn ep.
  rewrite ep /part_of size_filter -has_count.
  move: hn; rewrite mem_undup; case/mapP=> /= bn hbn ->; apply/hasP.
  by exists bn => //; rewrite /eq_hash /= eqxx.
  Qed.
   
  
  Lemma part_all_eq_hash (hd : B * nat) (tl : seq (B * nat)) (hm : hash_map) :
  (hd :: tl \in gen_partition hm) -> all (eq_hash hd.2) (hd::tl).
  Proof.
    case/mapP=> /= n hn.
    rewrite [X in X && _]eqxx /= => hfilter.
    apply/allP=> /= x tlx.
    have : x \in part_of hm n by rewrite -hfilter mem_cons.
    rewrite mem_filter /eq_hash; case/andP => /eqP-> _.
    have : hd \in part_of hm n by rewrite -hfilter mem_head.
    by rewrite mem_filter /eq_hash /pred1 /= eq_sym; case/andP.
  Qed.

Lemma part_all_eq_hash_mem (bn : B * nat) (l : seq (B * nat)) (hm : hash_map) :
  bn \in l -> (l \in gen_partition hm) -> all (eq_hash bn.2) l.
Proof.
case: l => [| x l] // hbn hxl.
suff -> : bn.2 = x.2 by apply: part_all_eq_hash hxl.
move: hxl; case/mapP=> n; rewrite mem_undup => hn e.
have : x \in part_of hm n by rewrite -e mem_head.
have : bn \in part_of hm n by rewrite -e.
by rewrite !mem_filter=> /andP [] /eqP<-  _ /andP [] /eqP<-.
Qed.

(* 

Lemma gen_partition_filter (hd a : B * nat) (tl : seq (B * nat)) (hm' : hash_map) :
    hd :: tl \in gen_partition [seq x <- hm' | (negb \o eq_hash a.2) x] -> 
    eq_hash hd.2 a = false.
  Proof.
  set hm := [seq x <- hm' | (negb \o eq_hash a.2) x].
  have : size hm < S (size hm) by apply ltnSn.
  have : all (negb \o eq_hash a.2) hm by apply filter_all.
  move: hm (size hm).+1.
  move=> hm n; move: n hm=> n.
  elim: n hd a => [//| n' IHn hd a hm] allPn measure.
  move: allPn; case: hm measure => [//|c l].
  autorewrite with gen_partition.
  rewrite in_cons=> measure allPn /orP[].
  + rewrite /=. rewrite eq_hash_refl=> /eqP[-> _].
    by move: allPn=> /=/andP[]; rewrite eq_hash_sym; case: (eq_hash c.2 a).
  apply IHn; last by rewrite /=eq_hash_refl/=; apply (leq_ltn_trans (size_filter_le _ l) measure).
  move: allPn; set hs := c :: l; rewrite all_filter=> allPn.
  apply /allP=> /=.
  move=> bn bnin; apply /implyP=> _.
  by have /=-> := in_all bnin allPn.
  Qed. *)
Lemma part_filter (hd : B * nat) (tl : seq (B * nat)) (hm : hash_map) :
    (hd :: tl \in gen_partition hm) -> hd :: tl = (partitionate hd.2 hm).1.
Proof.
case/mapP=> n hn e.
rewrite /partitionate /= e /part_of.
have : hd \in part_of hm n by rewrite -e mem_head.
by rewrite mem_filter; case/andP=> /eqP->.
Qed.

Lemma partP (hm : hash_map) (p : part) : p \in (gen_partition hm) ->
      exists (bn : B * nat), p = (partitionate bn.2 hm).1.
Proof. 
case/mapP=> /= n.
by rewrite mem_undup; case/mapP=> /= bn hbn -> {n} ->; exists bn.
Qed.

Lemma partition_memP (hm : hash_map) (p: part) :
  p \in (gen_partition hm) -> subseq p hm.
Proof. by case/partP=> [bn ->]; apply filter_subseq. Qed.
  Lemma partP' (hm : hash_map):
    forall (p : part), p \in (gen_partition hm) ->
      exists (bn : B * nat), bn \in p /\ p = (partitionate bn.2 hm).1.
  Proof.
  move=> p pin; have /part_size := pin; move: pin.
  case: p=> [//|hd tl] in_P.
  have /partition_memP in_hm := in_P.
  move/part_filter : in_P=> ->; exists hd; split=> [|//].
  rewrite mem_filter eq_hash_refl /=.
  by apply (mem_subseq in_hm); rewrite in_cons eqxx.
  Qed.


  Lemma all_mem_hash (p : part) (n : nat):
    all (eq_hash n) p -> constant (map snd p).
  Proof. 
  move=> hall.
  suff : all (pred1 n) [seq i.2 | i <- p] by move/all_pred1_constant. 
  by rewrite all_map.
  Qed.

  Lemma mem_constant (T : eqType) (t1 t2: T) (s : seq T):
    t1 \in s -> t2 \in s -> constant s -> t1 = t2.
  Proof.
  move=> t1in t2in /(constantP t1)[]x eq; move: t1in t2in.
  by rewrite eq !mem_nseq=> /andP[_ /eqP ->] /andP[_ /eqP ->].
  Qed.

  Lemma mem_partP (hm : hash_map) (bn : B * nat) (p : part) :
      bn \in p -> p \in (gen_partition hm) ->
        p = (partitionate bn.2 hm).1.
  Proof.
  move=>  hbn /mapP /= [n hn] ep.
  by move: hbn; rewrite ep /part_of mem_filter; case/andP => /eqP->.
  Qed.
 
  (* parts of size 1 *)
  Definition is_trivial (p : part) : bool := size p == 1.

  (* all parts are trivial *)
  Definition is_fine (P : partition) : bool := all is_trivial P.


  (* checks if t appears only one time in s *)
  Definition mult1 {T : eqType} (s : seq T) (t : T) :=
    count_mem t s == 1.

  (* number of uniq hashes in the hashmap *)
  Definition num_uniq_hash (hm : hash_map) :=
    count (mult1 (hashes_hm hm)) (hashes_hm hm).

  Lemma hashes_hm_cat (hm1 hm2 : hash_map):
    hashes_hm (hm1 ++ hm2) = hashes_hm hm1 ++ hashes_hm hm2.
  Proof. exact: map_cat. Qed.

  Lemma num_uniq_hash_cat (hm1 hm2 hm3 : hash_map) :
    perm_eq (hashes_hm hm2) (hashes_hm hm3) ->
    num_uniq_hash (hm1 ++ hm2) = num_uniq_hash (hm1 ++ hm3).
  Proof.
  elim: hm1=> [/=/permP eq| hd tl IHtl]; rewrite /num_uniq_hash.
  + by rewrite eq; apply eq_in_count=> /= h hin; rewrite /mult1 eq.
  rewrite /num_uniq_hash (hashes_hm_cat (hd::tl) hm2) (hashes_hm_cat (hd::tl) hm3) !count_cat.
  set s1:= hashes_hm (hd::tl).
  set s2:= hashes_hm hm2.
  set s3:= hashes_hm hm3.
  move=> /permP peq.
  congr addn; last first.
  + by rewrite /mult1/=; rewrite peq; apply eq_in_count=> /= s sin; rewrite !count_cat peq.
  apply eq_in_count=> /= n nin.
  rewrite /mult1 /=.
  set htl := hashes_hm tl.
  rewrite !count_cat.
  set m := hd.2 == n.
  set o := (count_mem n htl).
  by rewrite peq.
  Qed.

  Lemma num_uniq_hash_catC (hm1 hm2 : hash_map):
    num_uniq_hash (hm1 ++ hm2) = num_uniq_hash (hm2 ++ hm1).
  Proof.
  rewrite /num_uniq_hash.
  set s1 := hashes_hm (hm1 ++ hm2).
  set s2 := hashes_hm (hm2 ++ hm1).
  suffices /permP peq : perm_eq s1 s2.
    rewrite peq; apply eq_in_count.
    by move=> /= h hin; rewrite /mult1 peq.
  rewrite /s1 /s2 !hashes_hm_cat.
  by apply /permPl; apply perm_catC.
  Qed.

  (* number of trivial parts in a partition *)
Definition distinguished (hm : hash_map) : nat :=
    count is_trivial (gen_partition hm).

Lemma size_gen_partition (hm : hash_map) : size (gen_partition hm) <= size hm.
Proof.
rewrite /gen_partition size_map /hashes_hm.
by apply: leq_trans (size_undup _) _; rewrite size_map.
Qed.

  Lemma proj1_set_nth_prod (hm : hash_map) (b0 : B) (n0 i: nat):
    i < size hm ->
    hashes_hm (set_nth (b0, n0) hm i (b0, n0)) = set_nth n0 (hashes_hm hm) i n0.
  Proof.
  rewrite !set_nthE size_map -nat_coq_nat=> ->.
  by rewrite hashes_hm_cat {1 2}/hashes_hm map_take /= map_drop.
  Qed.

  Lemma partitionate_sndE (hd : B * nat) (tl : seq (B * nat)):
    (partitionate hd.2 (hd :: tl)).2 = [seq x <- hd :: tl | (negb \o eq_hash hd.2) x].
  Proof. by []. Qed.

Lemma count_mult (hm : hash_map) (n : nat):
    count (eq_hash n) hm = count_mem n (hashes_hm hm).
Proof. by rewrite /eq_hash count_map. Qed.

Lemma mult1_filter (n m : nat) (s: seq nat):
    n != m -> mult1 s m = mult1 (filter (predC1 n) s) m.
  Proof. by rewrite /mult1=> /(@count_mem_filter _ _ s) ->. Qed.
(* 
Lemma count_mult1_opt (hd : B * nat) (tl : seq (B * nat)):
    let ps := (partitionate hd.2 (hd :: tl)).2 : seq (B * nat) in
    count (mult1 (hashes_hm ps)) (hashes_hm ps) = 
    count (mult1 (hashes_hm (hd :: tl))) (hashes_hm tl).
  Proof.
  move=> ps.
  have e : ps = [seq x <- hd :: tl | (negb \o eq_hash hd.2) x] by [].
  rewr
    rewrite {2}/ps /partitionate. 
  Lemma count_mult1_opt (hd : B * nat) (tl : seq (B * nat)):
    let ps := (partitionate hd.2 (hd :: tl)).2 : seq (B * nat) in
    count (mult1 (hashes_hm ps)) (hashes_hm ps) = count (mult1 (hashes_hm (hd :: tl))) (hashes_hm tl).
  Proof.
  rewrite partitionate_sndE.
  move=> ps; set fhs := hashes_hm _.
  have /permEl := perm_filterC (negb \o eq_hash hd.2) tl.
  move=> /(perm_map snd)/permP <-.
  rewrite map_cat count_cat.
  set s_neq_hd := map _ _; set s_eq_hd := map _ _.
  have -> : fhs = s_neq_hd by rewrite /fhs/hashes_hm/ps/= eq_hash_refl/=.
  move=> {ps fhs}.
  suffices ->: count (mult1 (hashes_hm (hd :: tl))) s_eq_hd = 0.
    rewrite addn0; apply eq_in_count=>/= h /mapP[/= [b n]].
    rewrite mem_filter=> /andP[neq_hd in_tl] ->.
    move: neq_hd; rewrite /= /eq_hash/pred_eq/=.
    move=> /(mult1_filter _ _ (hd.2:: hashes_hm tl)) ->.
    suffices -> :s_neq_hd = [seq x <- hd.2 :: hashes_hm tl | predC1 hd.2 x] by [].
    rewrite {}/s_neq_hd=> {s_eq_hd in_tl}.
    elim: tl=> [/=|a tl' IHtl2]; first by case: ifP; move=> /negPf; rewrite eqxx.
    rewrite /= {4}/negb eqxx {4}/negb /eq_hash/pred_eq.
    case_eq (a.2 == hd.2); rewrite eq_sym /==> -> /=.
    by rewrite IHtl2; rewrite /predC1/= eqxx /=.
    by congr cons; rewrite IHtl2 /= eqxx /=.
  apply /eqP; rewrite -allPn_count.
  apply /allP=> /= shd /mapP[/= bn].
  rewrite mem_filter=> /andP[eq_hd mem_tl] ->.
  rewrite /mult1=> {s_neq_hd s_eq_hd shd}.
  move: eq_hd.
  rewrite /predC/= negbK/eq_hash/pred_eq=> ->.
  rewrite add1n /negb /=.
  move/perm_to_rem : mem_tl=> /(perm_map snd)/permP->.
  by rewrite /= eqxx add1n; case: (count_mem _ _).
  Qed. *)

Lemma num_triv_distinguished (hm : hash_map):
    distinguished hm = num_uniq_hash hm.
Proof.
rewrite /distinguished /gen_partition /num_uniq_hash /is_trivial.
rewrite count_map /preim /mult1 /= /part_of.
have /permP aux := (perm_count_undup (hashes_hm hm)).
rewrite -[in RHS]aux {aux} count_flatten -map_comp /=.
rewrite -[LHS]sumn_count; congr sumn.
apply: eq_map=> k /=; rewrite size_filter count_nseq -count_mult.
set n := count _ _.
by case: (n =P 1) => // ->; rewrite muln1.
Qed.

Lemma size_perm_gen_partition (hm p : hash_map):
      perm_eq (hashes_hm hm) (hashes_hm p) ->
       size (gen_partition hm) = size (gen_partition p).
Proof.
move=> hperm.
rewrite /gen_partition !size_map; apply: perm_size; apply: perm_undup.
exact: perm_mem.
Qed.

Lemma perm_hash_eq_fine (hm p : hash_map):
  perm_eq (hashes_hm hm) (hashes_hm p) -> is_fine (gen_partition hm) = is_fine (gen_partition p).
    Proof.
    move=> count_hashes.
    rewrite /is_fine.
    rewrite !all_count.
    suffices -> : count is_trivial (gen_partition hm) = count is_trivial (gen_partition p).
      by apply /idP/idP=> /eqP ->; apply /eqP; apply size_perm_gen_partition=> //; rewrite perm_sym.
    set c1 := count _ _.
    set c2 := count _ _.
    have -> : c1 = distinguished hm by [].
    have -> : c2 = distinguished p by [].
    rewrite !num_triv_distinguished /num_uniq_hash.
    rewrite -(permP count_hashes); apply eq_in_count; move=> h hin.
    by rewrite /mult1 -(permP count_hashes).
    Qed.

    (* The blank nodes of a hash map *)
    Definition bnodes_hm (hm : hash_map): seq B := map fst hm.

    Lemma bnodes_hm_exists (hm : hash_map) :
      forall b, b \in bnodes_hm hm -> exists n, (b,n) \in hm.
    Proof.
    by move=> b /mapP/=[[b' n] bin ->]/=; exists n.
    Qed.

    Lemma bnodes_hm_has_eq_bnodes (hm : hash_map) :
      forall b, b \in bnodes_hm hm -> has (eq_bnode b) hm.
    Proof.
    move=> b /bnodes_hm_exists/=[n bnin].
    apply /hasP; exists (b,n)=> //.
    by rewrite /eq_bnode/pred_eq /= eqxx.
    Qed.
 
    Lemma bnodes_hm_index_ltn (hm : hash_map) (b : B) :
      b \in bnodes_hm hm -> (index b (bnodes_hm hm) < size hm)%N.
    Proof.
    have -> : size hm = size (bnodes_hm hm) by rewrite size_map.
    by move=> h; rewrite index_ltn // take_size.
    Qed.

    Lemma bnodes_hm_index_size (hm : hash_map) (b : B) :
    b \in bnodes_hm hm -> (index b (bnodes_hm hm) == size hm = false)%N.
    Proof. by move/bnodes_hm_index_ltn/ltn_eqF. Qed.

    Lemma find_index_eq_bnode bs s (bn : B) :
      size s = size bs ->
      find (eq_bnode bn) (zip bs s) = index bn bs.
    Proof.
    elim: bs s => [| a l IHl]; first by move=> ?; rewrite zip0s.
    by case =>  [//| b l2] /= [eqsize_tl]; rewrite IHl /eq_bnode.
    Qed.

    Lemma find_index_eq_hash (bs: seq B) (s: seq nat) (bn : nat) :
      size s = size bs ->
      find (eq_hash bn) (zip bs s) = index bn s.
    Proof.
    elim: s bs => [| a l IHl] bs; first by move=> ?; rewrite zips0.
    by case: bs => [//| b l2] /= [eqsize_tl]; rewrite IHl //.
    Qed.

    Lemma hashes_filter_neq (n m : nat) (hm : hash_map) :
      (m == n) = false ->
        (n \in hashes_hm hm) =
          (n \in hashes_hm (filter (negb \o (fun p0 : B * nat => m == p0.2)) hm)).
    Proof.
    set p := negb \o (fun p0 : B * nat => m == p0.2).
    move=> neq.
    apply /idP/idP.
    elim: hm=> [//| h tl IHtl] /=.
    rewrite in_cons=> /orP[/eqP eq| in_tl].
    + by rewrite /p/= -eq neq /= in_cons eq eqxx.
    + case: h=> b n'; rewrite /p/=.
      case_eq (m != n')=> H; last by apply IHtl.
      by rewrite /=; apply inweak; apply IHtl.
    + move=> /mapP[/= bn ]. rewrite mem_filter=> /andP[].
      rewrite /p=>/= pbn bnin ->; move: bnin.
      elim: hm=> [//|hd tl IHtl].
      rewrite in_cons=> /orP[/eqP->|]; first by rewrite in_cons eqxx.
      by rewrite in_cons=> /IHtl ->; rewrite orbT.
    Qed.

    Lemma partitionate_filter (n m : nat) (hm : hash_map):
      (n == m) = false ->
        (partitionate n hm).1 = (partitionate n [seq x <- hm | (negb \o eq_hash m) x]).1.
    Proof.
    elim: hm=> [//| h tl IHtl] neq; rewrite /=/eq_hash/pred_eq.
    case: ifP=> [/eqP eq_nh2| ]/=; last first.
    + move=> neq_nh2; rewrite /negb.
      by case: ifP; case: ifP=> //neq_mh2 _ /=; rewrite ?neq_nh2; apply IHtl.
      rewrite eq_nh2 neq /= eq_nh2 eqxx; congr cons.
      have -> : [seq p <- tl | p.2 == n] = (partitionate n tl).1 by [].
      by rewrite IHtl.
  Qed.


Lemma part_in_partition (n : nat) (hm : hash_map) :
  n \in (hashes_hm hm) -> (partitionate n hm).1 \in gen_partition hm.
Proof.
case/mapP=> /= bn hbn ->. rewrite /gen_partition.
by apply/mapP; exists bn.2=> //; rewrite mem_undup; apply/mapP; exists bn.
Qed.

Lemma is_fine_uniq (hm : hash_map) :
   is_fine (gen_partition hm) -> uniq (hashes_hm hm).
Proof.
rewrite /is_fine all_map all_undup /preim=> /allP /= h.
apply: count_mem_uniq => /= x.
case hx: (x \in (hashes_hm hm)). (* improve*)
- have := (h _ hx). rewrite /is_trivial /part_of size_filter /eq_hash.
  by rewrite count_map; move/eqP->.
- rewrite count_map /preim /=; apply/eqP; move/negP/negP: hx. 
  apply: contraNT. rewrite -lt0n -has_count; case/hasP=> /= bn hbn /eqP<- {x}.
  by apply/mapP; exists bn.
Qed.

    (* passes the hash_map's keys under mu *)
    (* Definition map1 (T U R : Type) (f : T -> R) (tus : seq (T * U)) : seq (R * U) := *)
    (*   zip (map f (map fst tus)) (map snd tus). *)
Definition map1 (mu : B -> B) (h : hash_map) : hash_map :=
  zip (map mu (map fst h)) (map snd h).

    Lemma hashes_of_map1 (hm : hash_map) (mu : B -> B):
      hashes_hm (map1 mu hm) = hashes_hm hm.
    Proof. by elim: hm=> [//|hd tl /= ->]. Qed.

    Lemma map1_map (mu : B -> B):
      (* (map1 (U := nat) mu) =1 (map (fun p=> (mu p.1,p.2))). *)
      (map1 mu) =1 (map (fun p=> (mu p.1,p.2))).
    Proof.
    move=> hm; elim: hm=> [//|[b n] tl IHtl] /=.
    by rewrite /map1/= -IHtl.
    Qed.


  Lemma map1_zip (s1 : seq B)(s2 : seq nat) (f : B -> B) :
    size s1 = size s2 -> map1 f (zip s1 s2) = zip (map f s1) s2.
  Proof. by move=> eq_size; rewrite /map1 zip_proj1 // map_snd_zip_size. Qed.

  Lemma map1_bnodesC (hm: hash_map) (mu : B -> B):
    (bnodes_hm (map1 mu hm)) = map mu (bnodes_hm hm).
  Proof.
  rewrite /bnodes_hm map1_map -map_comp.
  have /eq_map -> : fst \o (fun p : B * nat => (mu p.1,p.2)) =1 mu \o fst by [].
  by rewrite map_comp.
  Qed.

End HashMapsAndPartitions.

Section Template.
  Variable disp : Order.disp_t.
  (* TODO : check that order is needed, since below comes a comparison comp on graphs *)
  Variable I B L : orderType disp.
  Notation le_triple := (@le_triple disp I B L).


(* Enumeration of b-nodes *)
  Hypothesis nat_inj : nat -> B.
  Hypothesis nat_inj_ : injective nat_inj.

  (* comparison on graphs, morally an order relation. *)

  Variable (cmp : seq (triple I B L) -> seq (triple I B L) -> bool).

  Hypothesis cmp_anti : antisymmetric cmp.
  Hypothesis cmp_total : total cmp.
  Hypothesis cmp_trans : transitive cmp.

  Lemma cmp_refl (g : seq (triple I B L)) : cmp g g.
  Proof. by move: (cmp_total g g); move=> /orP[]. Qed.

  Definition choose_graph (g1 g2 : seq (triple I B L)) :=
    if cmp g1 g2 then g2 else g1.

  Lemma choose_graphA : associative choose_graph.
  Proof.
  move=> g h i; rewrite /choose_graph.
  repeat (try case : ifP); rewrite //.
  + by move=> _ ->.
  + by move=> ghn ->.
  + by move=> _ ->.
  + by move=> gh hi; rewrite (cmp_trans gh hi).
  + by move=> _ ->.
  + by move=> _ ->.
  + move=> ghn gi hin _.
    move: (cmp_total g h) (cmp_total h i); rewrite ghn hin /==> hg ih {ghn hin}.
    have hi := (cmp_trans hg gi).
    have eq_hi : h = i by apply cmp_anti; rewrite hi ih.
    by apply cmp_anti; rewrite gi -eq_hi hg.
  Qed.

  Lemma choose_graphC : commutative choose_graph.
  Proof.
  move=> x y; rewrite /choose_graph; case: ifP; case: ifP=> //.
  + by move=> yx xy; apply cmp_anti; apply /andP.
  + by move=> yxn xyn; move: (cmp_total x y); rewrite xyn yxn.
  Qed.

  Lemma choose_graph_idem : idempotent choose_graph.
  Proof.
  by move=> x; rewrite /choose_graph cmp_refl.
  Qed.

  (* A default graph *)
  Definition g0 : seq (triple I B L) := [::].

  (* Determines a choice of default graph can *)
  Hypothesis can_extremum : forall (x : seq (triple I B L)), cmp g0 x.

  Lemma can_lid : left_id g0 choose_graph.
  Proof. by move=> x; rewrite /choose_graph can_extremum. Qed.

  HB.instance Definition _ :=
    Monoid.isComLaw.Build
      (seq (triple I B L)) g0
      (choose_graph) choose_graphA
      choose_graphC
      can_lid.

  Local Notation hash_map := (@hash_map B).
  Local Notation part := (@part B).
  Local Notation partition := (@partition B).

  Arguments eq_hash {B} _ _.
  Arguments eq_bnode {B} _ _.

(* Relabeling induced by hashmap hm: for b in hm, 
   outputs the corresponding B-node b to its hash in hm, behaves as
   identity outside hm *)
  Definition fun_of_hash_map (hm : hash_map) : B -> B :=
      fun b =>
      let the_label := index b (bnodes_hm hm) in 
       if the_label == size hm then b 
      else nat_inj (nth (b, 0) hm the_label).2.

(*      
Definition fun_of_hash_map (hm : hash_map) : B -> B :=
            fun b =>
              if has (eq_bnode b) hm then
                let the_label := nth O (map snd hm) (find (eq_bnode b) hm) in
                nat_inj the_label
              else
                b.
  *)    

  Lemma shift_hm (hm : hash_map) (f : B -> B) (x : B) :
    x \in bnodes_hm hm -> {in bnodes_hm hm &, injective f} -> (fun_of_hash_map (map1 f hm)) (f x) = (fun_of_hash_map hm) x.
  move=> hxin injf.
  rewrite /fun_of_hash_map.
  rewrite bnodes_hm_index_size; last by rewrite map1_bnodesC map_f.
  rewrite bnodes_hm_index_size //. congr nat_inj.
  rewrite map1_bnodesC index_map_in //.
  set i := index _ _.
  by rewrite map1_map (nth_map (x,0)) //= bnodes_hm_index_ltn.
  Qed.

  Lemma inj_uniq_good_hm (hm : hash_map) (f: B -> B) (x : B) :
    forall g : seq (triple I B L), x \in get_bts g ->
                                    bnodes_hm hm =i get_bts g -> {in get_bts g &, injective f} ->
                                    (fun_of_hash_map (map1 f hm)) (f x) = (fun_of_hash_map hm) x.
  Proof.
  move=> g x_in mem_eq inj_f; apply shift_hm; first by rewrite mem_eq.
  by move=> x' y xin yin; apply inj_f; rewrite -mem_eq.
  Qed.

Coercion fun_of_hash_map : hash_map >-> Funclass.

Lemma bnodes_hmP (hm : seq (B * nat)) b : reflect (exists n, (b, n) \in hm) (b \in bnodes_hm hm).
Proof.
apply: (iffP idP) => /=.
- by rewrite /bnodes_hm; case/mapP=> k hk ->; exists k.2; case: k hk.
- by case=> k hbk; apply/mapP; exists (b, k).
Qed.

Lemma has_eq_bnodes (hm : seq (B * nat)) b : 
  has (eq_bnode b) hm = (b \in bnodes_hm hm).
Proof.
apply/hasP/mapP=> /= [] [] x hmx /eqP hx; exists x=> //.
by move/eqP: hx=> ->; exact: eqxx.
Qed.

Lemma perm_eq_bnodes_hm (hm1 hm2 : seq (B * nat)) : 
  perm_eq hm1 hm2 -> perm_eq (bnodes_hm hm1) (bnodes_hm hm2).
Proof. by move=> e; rewrite /bnodes_hm; apply: perm_map. Qed. 


Lemma index_hashes (hm : seq (B * nat)) (b : B) (n : nat) :
  (b, n) \in hm -> 
  uniq (hashes_hm hm) ->
  index (b, n) hm = index n (hashes_hm hm).
Proof.
move=> hin huniq.
rewrite -[X in index X (hashes_hm _)]/((b,n).2) index_map_in // {b n hin}.
move=> u v uin vin e.
pose i := index u hm.
pose j := index v hm.
suff eij : i = j by rewrite -(nth_index u uin) -(nth_index u vin) -/i eij.
move/uniqP: huniq => /(_ u.2 i j). 
rewrite size_map !inE !index_mem; apply=> //.
rewrite (nth_map u) ?index_ltn // ?take_size //. 
rewrite (nth_map v) ?index_ltn // ?take_size //.
by rewrite !nth_index.
Qed.

Lemma index_bnodes {hm : seq (B * nat)} {b : B} {n : nat} :
  (b, n) \in hm -> 
  uniq (bnodes_hm hm) ->
  index (b, n) hm = index b (bnodes_hm hm).
Proof.
move=> hin huniq.
rewrite -[X in index X (bnodes_hm _)]/((b,n).1) index_map_in // {b n hin}.
move=> /= u v uin vin e.
pose i := index u hm.
pose j := index v hm.
suff eij : i = j by rewrite -(nth_index u uin) -(nth_index u vin) -/i eij.
move/uniqP: huniq => /(_ u.1 i j). 
rewrite size_map !inE !index_mem; apply=> //.
rewrite (nth_map u) ?index_ltn // ?take_size //. 
rewrite (nth_map v) ?index_ltn // ?take_size //.
by rewrite !nth_index.
Qed.

Lemma uniq_bnode_hm (hm : seq (B * nat)) : uniq (bnodes_hm hm) -> 
  forall b n1 n2, (b, n1) \in hm -> (b, n2) \in hm -> n1 = n2.
Proof.
move=> /= hu b n1 n2 h1 h2.
have hbnodes : b \in bnodes_hm hm by apply/mapP; exists (b, n1).
suff e : index (b, n1) hm = index (b, n2) hm.
  suff : (b, n1) = (b, n2) by case.
  by rewrite -(nth_index (b, n1) h1) -(nth_index (b, n1) h2) e.
by rewrite !index_bnodes.
Qed.

Lemma find_eq_bnode (hm : seq (B * nat)) b : 
  find (eq_bnode b) hm = index b (bnodes_hm hm).
Proof.
(* move=> ubhm.*)
by rewrite [hm]hm_zip find_index_eq_bnode ?size_map // -hm_zip.
Qed.

Lemma fun_of_hash_perm (hm p : hash_map) :
                uniq (bnodes_hm hm) ->
                perm_eq hm p ->
                {in (bnodes_hm hm), fun_of_hash_map hm =1 p}.
  Proof.
  move=> huniq eq_hm_p b hmb.
  rewrite /fun_of_hash_map.
  set i := index _ _.
  set j := index _ _.
  have i_small : (i < size hm)%N.
    have -> : size hm = size (bnodes_hm hm) by rewrite [RHS]size_map. 
  by rewrite index_ltn ?take_size. 
  have j_small : (j < size p)%N.
    have -> : size p = size (bnodes_hm p) by rewrite [RHS]size_map. 
    rewrite index_ltn ?take_size //.
    by move/perm_eq_bnodes_hm/perm_mem: eq_hm_p=> <-.
  rewrite  (ltn_eqF i_small) (ltn_eqF j_small). 
  suff -> : nth (b, 0) hm i = nth (b, 0) p j by [].
  set x := LHS; set y := RHS.
  case/bnodes_hmP: hmb=> k bkhm.
  have bkp : (b, k) \in p by rewrite  -(perm_mem eq_hm_p).
  have huniqp : uniq (bnodes_hm p).
    by move/perm_eq_bnodes_hm/perm_uniq : eq_hm_p<-.
  rewrite /x -[i](index_bnodes bkhm)=> //. 
  rewrite /y -[j](index_bnodes bkp) //.
  by rewrite !nth_index.
  Qed.

    Lemma nth_funof (g : seq (triple I B L)) (hm : hash_map) :
      bnodes_hm hm =i get_bts g ->
        is_fine (gen_partition hm) ->
          forall (b : B) dfb dfn (bin : b \in get_bts g),
            exists n, (nth (dfb, dfn) hm (index b [seq i.1 | i <- hm])) = (b,n).
    Proof.
    move=> mem_eq fine b bdf dfn; rewrite -mem_eq.
    exists (nth dfn [seq i.2 | i <- hm] (index b [seq i.1 | i <- hm])).
    rewrite (hm_zip hm) nth_zip; last by rewrite size_proj.
    by rewrite -hm_zip; congr pair; rewrite nth_index.
    Qed.

    Lemma funof_snd_inj (g : seq (triple I B L)) (hm : hash_map) :
      bnodes_hm hm =i get_bts g ->
        is_fine (gen_partition hm) ->
          {in hm &, injective [eta snd]}.
    Proof.
    rewrite (hm_zip hm); set hm' := zip _ _.
    move=> mem_eq fine uhm /= bn bn' bnin bn'in.
    eapply (zip_uniq_proj2 )=> //.
    + by apply is_fine_uniq; apply fine.
    + by symmetry; apply size_proj.
    + by rewrite -hm_zip.
    + by rewrite -hm_zip.
    Qed.

    Lemma uniq_get_bts_is_fine (g : seq (triple I B L)) hm :
      bnodes_hm hm =i get_bts g ->
        is_fine (gen_partition hm) ->
          uniq [seq fun_of_hash_map hm i | i <- get_bts g].
    Proof.
    move=> mem_eq /is_fine_uniq fine.
    apply /in_map_injP; first by apply uniq_get_bts.
    move=> b b'; rewrite -!mem_eq=> bin b'in.
    rewrite /fun_of_hash_map.
    rewrite !bnodes_hm_index_size // => /nat_inj_.
    have eqsize: size [seq i.2 | i <- hm] = size [seq i.1 | i <- hm] by apply size_proj.
    set i := index _ _.
    set j := index _ _.
    move=> heq.
    suffices e : i = j.
      by rewrite -(nth_index b bin) -(nth_index b b'in) -/i e.
    move: heq.
      have<- : nth 0 (hashes_hm hm) i = (nth (b, 0) hm i).2.
      apply: nth_map; exact: bnodes_hm_index_ltn.
    have<- : nth 0 (hashes_hm hm) j = (nth (b', 0) hm j).2.
      apply: nth_map; exact: bnodes_hm_index_ltn.
    by move/uniqP: fine;apply; rewrite size_map; exact: bnodes_hm_index_ltn.   
    Qed.

    Lemma uniq_label_is_fine (g : seq (triple I B L)) (ug: uniq g) (hm : hash_map) :
      bnodes_hm hm =i get_bts g ->
        is_fine (gen_partition hm) ->
          uniq (relabeling_seq_triple (fun_of_hash_map hm) g).
    Proof.
    move=> mem_eq fine.
    have := uniq_get_bts_is_fine _ _ mem_eq fine.
    move=> /(in_map_injP _ (uniq_get_bts _)) mu_inj.
    by rewrite map_inj_in_uniq=> //; apply inj_get_bts_inj_ts.
    Qed.


  (* blank nodes of g and blank nodes of hm are set equal *)
  Definition hash_map_for (g : seq (triple I B L)) (hm : hash_map) :=
    bnodes_hm hm =i get_bts g.

  Definition good_hash_map_for (g : seq (triple I B L)) (hm : hash_map) :=
    forall (mu : B -> B),
      {in get_bts g &, injective mu} ->
        {in get_bts g, ((map1 mu hm) \o mu) =1 hm}.

  Lemma eq_mem_good_hm (g : seq (triple I B L)) (hm : hash_map) :
    hash_map_for g hm -> good_hash_map_for g hm.
  Proof.
  move=> hm_for_g mu mu_inj x xin.
  apply shift_hm; first by rewrite hm_for_g.
  move=> {}x y {}xin yin.
  by apply mu_inj; rewrite -hm_for_g.
  Qed.

  (* Initial hash map from a graph *)
  Variable (init_hash : seq (triple I B L) -> hash_map).

  (* init_hash g has the same bnodes as the graph g *)
  (* TODO: use hash_map_for *)
  Hypothesis good_init :
    forall (g : seq (triple I B L)), bnodes_hm (init_hash g) =i get_bts g.

  (* the relabeling under injective functions "commutes" with init_hash modulo permutation *)
  Hypothesis init_hash_inj_rel : forall (g : seq (triple I B L)) (mu: B -> B),
      {in (get_bts g)&, injective mu} -> perm_eq (map1 mu (init_hash g)) (init_hash (relabeling_seq_triple mu g)).

  (* permutation equal graphs yield permutation equal hashmaps under init_hash *)
  Hypothesis init_hash_perm_graph : forall (g h : seq (triple I B L)), perm_eq g h -> perm_eq (init_hash g) (init_hash h).

  (* the result of init_hash has uniq blank nodes *)
  Hypothesis init_hash_ubs : forall (g : seq (triple I B L)), uniq (bnodes_hm (init_hash g)).

  (* TODO : remove Lemma init_hash_inv : forall (g : seq (triple I B L)), *)
  (*   good_hash_map_for g (init_hash g). *)
  (* Proof. *)
  (* move=> g mu mu_inj x xin. *)
  (* apply shift_hm. *)
  (* by rewrite good_init. *)
  (* move=> {}x y {}xin yin. *)
  (* by apply mu_inj; rewrite -good_init. *)
  (* Qed. *)

  (* init hash yeilds a good hash for its input *)
  (* TODO remove *)
    (* Hypothesis init_hash_inv : forall (g : seq (triple I B L)), *)
    (*     good_hash_map_for g (init_hash g). *)

  (* Pick a part p from a failed attempt at computing a fine partition from the input hashmap hm. Expected:
     - (map fst p) is included in (map fst hm)
     - elements of p have the same hash
     - p is non empty and non singleton *)
  Variable choose_part : hash_map -> part.
  (* all nodes in choose_part hm lead to bnodes of hm. NOTE that the assumption does not prevent choose_part from duplicating elements. *)
  (* Variable choose_hash : hash_map -> nat. *)
  (* TODO : relate choose_part and choose_hash *)
  (* choose_part selection is based on the hashes of the input *)
  
  Hypothesis choose_part_order :
    forall (hm1 hm2 : hash_map),
  (* Assia : it seems to me that this assumption can only be too weak 
      perm_eq (hashes_hm hm1) (hashes_hm hm2) ->  *)
    perm_eq hm1 hm2 ->
        perm_eq (choose_part hm1) (choose_part hm2).

  (* choose_part commutes with map1 *)
  Hypothesis choose_part_post_relabeling :
    forall (hm: hash_map)(mu : B -> B), choose_part (map1 mu hm) = map1 mu (choose_part hm).


  (* choose_part hm is subset of hm *)
  Hypothesis in_part_in_hm :
    forall (bn : B * nat) hm, bn \in choose_part hm -> bn \in hm.

  (* TODO : change into ... != [::] *)
  (* if the partition is not fine, then choose_part yields a non empty sequence *)
  Hypothesis choose_from_not_fine :
    forall (hm : hash_map),
      ~~ is_fine (gen_partition hm) -> choose_part hm == [::] = false.

  Lemma in_part_in_bnodes (bn : B * nat) hm: bn \in choose_part hm -> bn.1 \in bnodes_hm hm.
  Proof.
  move/in_part_in_hm; rewrite /bnodes_hm; rewrite {1}(hm_zip hm).
  by case: bn=> [b n] /in_zip/andP[->].
  Qed.

  (* update a hashmap from an input graph, without increasing the measure *)
  Variables (color color_refine : seq (triple I B L) -> hash_map -> hash_map).

  (* Hypothesis for color *)

  (* coloring a hashmap preserves being a hash_map for *)
  (* TODO : use hash_map_for *)
  Hypothesis color_good_hm :
    forall (g : seq (triple I B L)) hm,
      bnodes_hm hm =i get_bts g -> bnodes_hm (color g hm) =i get_bts g.

  (* coloring a hashmap preserves beign a good hash_map for *)
  (* TODO remove *)
  (* Hypothesis color_inv : forall (g : seq (triple I B L)) (hm : hash_map), *)
  (*     good_hash_map_for g hm -> good_hash_map_for g (color g hm). *)

  (* the coloring of a relabeling is the relabeling of a coloring *)
  Hypothesis color_post_relabeling : forall (g : seq (triple I B L)) (mu : B -> B) (hm : hash_map),
    {in (get_bts g)&, injective mu} ->
      {in (bnodes_hm hm)&, injective mu} ->
        perm_eq (color (relabeling_seq_triple mu g) (map1 mu hm)) (map1 mu (color g hm)).

  (* graphs equal up to permutation yield hashmaps equal up to permutation under color and the same hashmap *)
  Hypothesis color_perm_graph : forall (g h : seq (triple I B L)) (hm : hash_map),
      perm_eq g h -> perm_eq (color g hm) (color h hm).

  (* hashmaps equal up to permutation yield hashmaps equal up to permutation under color of the same graph *)
  (* TODO invert order of perm_eq hyp of hashes *)
  Hypothesis color_perm_hm : forall (hm p : hash_map),
      perm_eq p hm -> forall (g : seq (triple I B L)), perm_eq (color g hm) (color g p).

  (* color preserves uniqueness of blank nodes *)
  Hypothesis color_ubs : forall (hm: hash_map) (g : seq (triple I B L)), (uniq (bnodes_hm hm)) -> uniq (bnodes_hm (color g hm)).


  (* Hypothesis for color_refine *)
  (* Same for color_refine *)
  (* TODO : use hash_map_for *)
  Hypothesis color_refine_good_hm :
    forall (g : seq (triple I B L)) hm,
      bnodes_hm hm =i get_bts g -> bnodes_hm (color_refine g hm) =i get_bts g.
  (* TODO remove *)
  (* Hypothesis color_refine_inv : forall (g : seq (triple I B L)) (hm : hash_map), *)
  (*     good_hash_map_for g hm -> good_hash_map_for g (color_refine g hm). *)

  Hypothesis color_refine_post_relabeling : forall (g : seq (triple I B L)) (hm : hash_map) (mu : B -> B),
           {in (get_bts g)&, injective mu} ->
           {in (bnodes_hm hm)&, injective mu} ->
           perm_eq (color_refine (relabeling_seq_triple mu g) (map1 mu hm))
                   (map1 mu (color_refine g hm)).

  Hypothesis color_refine_perm_graph : forall (g h: seq (triple I B L)) (hm : hash_map), perm_eq g h -> perm_eq (color_refine g hm) (color_refine h hm).

  Hypothesis color_refine_perm_hm : forall (g : seq (triple I B L)) (hm p: hash_map), perm_eq hm p -> perm_eq (color_refine g hm) (color_refine g p).

  Hypothesis color_refine_ubs : forall (hm: hash_map) (g : seq (triple I B L)), (uniq (bnodes_hm hm)) -> uniq (bnodes_hm (color_refine g hm)).

  Lemma color_of_iso (g h : seq (triple I B L)):
    forall (mu: B -> B),
    is_effective_iso_ts g h mu->
    perm_eq (map1 mu (color g (init_hash g))) (color h (init_hash h)).
  Proof.
  move=> mu /and3P[piso urel peq].
  have peq_col: perm_eq (color (relabeling_seq_triple mu g) (init_hash (relabeling_seq_triple mu g))) (color h (init_hash h)).
    have /color_perm_hm/(_ h) step : perm_eq (init_hash (relabeling_seq_triple mu g)) (init_hash h).
      by apply init_hash_perm_graph.
    by rewrite perm_sym; apply (perm_trans step) ; apply color_perm_graph; rewrite perm_sym.
  apply: (perm_trans _ peq_col).
  have step : perm_eq (color (relabeling_seq_triple mu g) (init_hash (relabeling_seq_triple mu g))) (color (relabeling_seq_triple mu g) (map1 mu (init_hash g))).
    by apply color_perm_hm; apply init_hash_inj_rel; apply (is_pre_iso_ts_inj piso).
  have mu_inj := (is_pre_iso_ts_inj piso).
  rewrite perm_sym. apply: (perm_trans step). apply color_post_relabeling=> //.
  by move=> b1 b2; rewrite !good_init; apply mu_inj.
  Qed.

  Lemma iso_color_fine :
    forall (g h : seq (triple I B L)),
      effective_iso_ts g h ->
      is_fine (gen_partition (color g (init_hash g)))
      = is_fine (gen_partition (color h (init_hash h))).
  Proof.
  move=> g h [mu /and3P[piso urel peq]].
  apply: perm_hash_eq_fine.
  rewrite -(hashes_of_map1 (color g (init_hash g)) mu).
  by apply perm_map; apply color_of_iso; apply /and3P;split.
  Qed.

  (* Marks a bnode in a hashmap*)
  Variable (mark : B -> hash_map -> hash_map).
  (* Hypothesis on mark *)

  Hypothesis good_mark :
    forall (g : seq (triple I B L)) (hm : hash_map),
      bnodes_hm hm =i get_bts g ->
      forall b, b \in bnodes_hm hm -> bnodes_hm (mark b hm) =i get_bts g.

  (* TODO: remove Hypothesis mark_inv : *)
  (*   forall (g : seq (triple I B L)) (hm : hash_map) (b : B), *)
  (*   get_bts g =i bnodes_hm hm -> *)
  (*     b \in (get_bts g) -> *)
  (*      uniq (bnodes_hm hm) -> *)
  (*       good_hash_map_for g hm -> *)
  (*         good_hash_map_for g (mark b hm). *)

  (* marking the mapping of an injective function is the mapping of the marking *)
  Hypothesis mark_post_rel: forall (b : B) (hm : hash_map) (mu : B -> B),
      b \in bnodes_hm hm -> 
         {in (bnodes_hm hm)&, injective mu} ->
         perm_eq (mark (mu b) (map1 mu hm)) (map1 mu (mark b hm)).

  Hypothesis mark_perm_hm : forall (b : B) (hm p : hash_map), 
  uniq (bnodes_hm hm) ->
  b \in bnodes_hm hm ->
  perm_eq hm p -> perm_eq (mark b hm) (mark b p).

  (* Marking a hashmap with one of its bnodes does not change its bnodes (but only the hashes)*)
  (* TODO : use hash_map_for *)
  Hypothesis mark_ubs : forall (hm: hash_map),
      (uniq (bnodes_hm hm))
      -> forall (b : B), b \in (bnodes_hm hm)
      -> uniq (bnodes_hm (mark b hm)).

  (* TODO : to be simplified into
    Hypothesis good_mark : forall (hm : hash_map),
     forall b, b \in bnodes_hm hm -> bnodes_hm (mark b hm) =i bnodes_hm hm.
   *)

  (* Measure on hash_map*)
  Variable (M : hash_map -> nat).

  (* Mark decreases the measure *)
  Hypothesis markP :
    forall (bn : B * nat) (hm : hash_map),
      (* TODO IMPORTANT : add this hypothesis *)
       ~~ is_fine (gen_partition hm) -> 
        uniq (bnodes_hm hm) -> 
      bn \in choose_part hm -> M (mark bn.1 hm) < M hm.

  (* color_refine does not increase the measure *)
  Hypothesis color_refineP :
    forall (g : seq (triple I B L)) (hm : hash_map),
      M (color_refine g hm) <= M hm.

  Lemma color_hm_for (g : seq (triple I B L)) : hash_map_for g (color g (init_hash g)).
  Proof. by apply color_good_hm; apply good_init. Qed.

  Lemma iso_color_fine_can (g h : seq (triple I B L)):
      effective_iso_ts g h ->
      relabeling_seq_triple (color g (init_hash g)) g
      =i relabeling_seq_triple (color h (init_hash h)) h.
  Proof.
  move=> [mu /and3P[piso urel peq]].
  have mu_inj := is_pre_iso_ts_inj piso.
  have : good_hash_map_for g (color g (init_hash g)).
    apply eq_mem_good_hm; apply color_hm_for.
  rewrite /good_hash_map_for=> /(_ _ mu_inj)/relabeling_seq_triple_ext_in <-.
  move=>/= t; rewrite -(eq_mem_map _ (perm_mem peq)) -relabeling_triple_comp_map.
  suffices : {in get_bts g, (map1 mu (color g (init_hash g))) \o mu =1 (color h (init_hash h)) \o mu}.
    move=> /relabeling_seq_triple_ext_in.
    rewrite -relabeling_triple_comp_map=> ->.
    by rewrite relabeling_triple_comp_map.
  move=> b bin /=.
  suffices mem_eq : bnodes_hm (color g (init_hash g)) =i get_bts g.
    apply fun_of_hash_perm.
    + rewrite map1_bnodesC.
    suffices col_ubs: uniq (bnodes_hm (color g (init_hash g))).
      rewrite map_inj_in_uniq //.
      by move=> b1 b2; rewrite !mem_eq; apply mu_inj.
    by apply color_ubs; apply init_hash_ubs.
    + by apply color_of_iso; apply /and3P; split.
    + by rewrite map1_bnodesC; move: bin; rewrite -mem_eq=> /(map_f mu).
  by move=> b'; rewrite color_good_hm.
  Qed.


  Section Distinguish.

    Lemma rem_swap (T : eqType) (s : seq T) (x y : T):
      rem x (rem y s) = rem y (rem x s).
    Proof.
    elim: s=> [//| h tl IHtl] /=.
    case: ifP.
    + move=> /eqP eqhy; rewrite eqhy.
      case: ifP; first by move /eqP ->.
      by rewrite /= eqxx.
    + move=> neq_hy; case: ifP; first by move=> /eqP -> /=; rewrite eqxx.
      by move=> neq_hx /=; rewrite neq_hx neq_hy IHtl.
    Qed.

    Definition ifb {T : Type} (b : bool) (f : b = true -> T) (g : b = false -> T) :=
      (if b then f else g) erefl.


      Equations? foldl_In {T R : eqType} (s : seq T) (f : R -> forall (y : T), y \in s -> R) (z : R) : R :=
      foldl_In nil f z := z;
      foldl_In (a :: l) f z := foldl_In l (fun x y inP=> f x y _) (f z a _).
    Proof.
    by rewrite in_cons inP orbT.
    by rewrite in_cons eqxx.
    Qed.
  
    Lemma foldl_foldl_eq {T R : eqType} (s : list T) (f : R -> T -> R) z :
      @foldl_In _ _ s (fun (r:R) (t:T) (_ : t \in s) => f r t) z = foldl f z s.
    Proof.
    funelim (foldl_In s _ z).
    - by [].
    - autorewrite with foldl_In; apply H.
    Qed.
  
  Equations? distinguish__
    (g : seq (triple I B L))
      (hm : hash_map)
      (gbot : seq (triple I B L))
      : seq (triple I B L) by wf (M hm) lt :=
    distinguish__ g hm gbot :=
    @ifb _ ((is_fine (gen_partition hm)) || ~~ (uniq (bnodes_hm hm))) (fun _ => nil) (fun _ =>
    let p := choose_part hm in
    let d := fun bn inP =>
               let hm' := color_refine g (mark bn.1 hm) in
               let fine := is_fine (gen_partition hm') in
               if fine then
                 let candidate := sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g) in
                 candidate
               else (distinguish__ g hm' gbot) in
    let f := fun gbot bn inP  =>
               let candidate := d bn inP in
               if cmp gbot candidate then candidate else gbot in
    foldl_In p f gbot).
    Proof.
    apply /ssrnat.ltP; apply (leq_ltn_trans (color_refineP _ _)).
    suff [e1 e2] : ~~ is_fine (gen_partition hm) /\ uniq (bnodes_hm hm).
      by exact: (markP (s, n)).
    by apply/andP; rewrite -[_ && _]negbK negb_and negbK e. (* BUG? Search _ negb orb. *)
    Qed.


Definition distinguish (g : seq (triple I B L)) (hm : hash_map) : seq (triple I B L) :=
      distinguish__ g hm g0.

Definition distinguish_ (g : seq (triple I B L)) (hm : hash_map) : seq (triple I B L) :=
      let p := choose_part hm in
	    let d := fun bn =>
	               let hm' := color_refine g (mark bn.1 hm) in
	               if is_fine (gen_partition hm') then
	                 let candidate := sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g) in
	                 candidate
	               else (distinguish g hm') in
      let f := fun gbot bn  =>
                 let candidate := d bn in
                 if cmp gbot candidate then candidate else gbot in
      foldl f g0 p.

    Lemma eq_distinguish (g : seq (triple I B L)) (hm : hash_map) :
    ~~ (is_fine (gen_partition hm)) -> (uniq (bnodes_hm hm)) -> distinguish g hm = distinguish_ g hm.
    Proof.
    move=> e1 e2.
    rewrite /distinguish.
    simp distinguish__.
    rewrite /ifb e2 (negPf e1) /=.
    rewrite /distinguish_ -foldl_foldl_eq /=.
    by autorewrite with distinguish__.
    Qed.

    Definition canonicalize (g : seq (triple I B L)) (hm : hash_map)
      (bn : (B * nat)) :=
	      let hm' := color_refine g (mark bn.1 hm) in
	      if is_fine (gen_partition hm') then
	        let candidate := sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g) in (* TODO simplfy let *)
	        candidate
	      else (distinguish g hm').

    Definition distinguish_fold (g : seq (triple I B L)) (hm : hash_map) : seq (triple I B L) :=
      let p := choose_part hm in
      foldl choose_graph g0 (map (canonicalize g hm) p).

    Lemma fold_map (T1 T2 R : Type) (f : R -> T2 -> R) (g : T1 -> T2) (z : R) (s : seq T1) :
      foldl (fun r1 t1=> f r1 (g t1)) z s = foldl f z (map g s).
    Proof. by elim: s z=> [//| a tl IHl] /= z; rewrite -IHl. Qed.

    Lemma distinguish_fold_map (g : seq (triple I B L)) (hm : hash_map) :
    ~~ (is_fine (gen_partition hm)) -> (uniq (bnodes_hm hm)) -> distinguish g hm = distinguish_fold g hm.
    Proof. 
    move=> e1 e2. 
    by rewrite /distinguish_fold eq_distinguish /distinguish_ // -fold_map. 
    Qed.

    Definition template (g : seq (triple I B L)) :=
      let hm := init_hash g in
      let hm' := color g hm in
      let iso_g := if is_fine (gen_partition hm')
                   then (sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g))
                   else distinguish g hm' in
      iso_g.

    Lemma distinguish_choice_default (gs: seq (seq (triple I B L))) (x0: seq (triple I B L)) :
      let ans := foldl choose_graph x0 gs in
     ans = x0 \/ ans \in gs.
    Proof.
    move=> ans; rewrite /ans{ans}.
    elim: gs x0 => [//| t ts IHts] x0; first by left.
    + rewrite in_cons /=. case: (IHts (choose_graph x0 t))=> [ -> |intail] /=.
    - rewrite /choose_graph; case: ifP=> _; first by right; rewrite eqxx.
      * by left.
    - by right; rewrite intail orbT.
    Qed.

    Lemma distinguish_choice (g : seq (triple I B L)) (hm: hash_map) :
    ~~ (is_fine (gen_partition hm)) -> (uniq (bnodes_hm hm)) -> 
    distinguish g hm = g0 \/ distinguish g hm \in (map (canonicalize g hm) (choose_part hm)).
    Proof. 
    move=> e1 e2. 
    by rewrite distinguish_fold_map //; apply distinguish_choice_default. 
    Qed.

    Lemma uniq_distinguish (g : seq (triple I B L)) (ug: uniq g) hm :
    ~~ (is_fine (gen_partition hm)) -> (uniq (bnodes_hm hm)) ->
    bnodes_hm hm =i get_bts g -> (negb \o (is_fine (B:=B))) (gen_partition hm) -> uniq (distinguish g hm).
    Proof.
    move=> e1 e2.
    have : M hm < S (M hm) by apply ltnSn.
    move: hm e1 e2 (M hm).+1.
    move=> hm e1 e2 n. move: n hm e1 e2 => n.
    elim: n => [//| n IHn hm e1 e2].
    case: (distinguish_choice g hm e1 e2); first by move=> ->.
    move=> /mapP/= [bn pin ->].
    move=> MH eqbns finePn.
    rewrite /canonicalize.
    case: ifP=> [fine|finePn1].
    -  rewrite sort_uniq; apply uniq_label_is_fine=> //; apply color_refine_good_hm.
       by apply (good_mark _ _ eqbns); apply in_part_in_bnodes.
    - apply IHn.
      + by rewrite finePn1.
      + apply: color_refine_ubs; apply: mark_ubs=> //.
        exact: in_part_in_bnodes.
      + apply: Order.POrderTheory.le_lt_trans (color_refineP _ _) _.
        by apply: Order.POrderTheory.lt_le_trans (markP _ _ _ _ _) MH.
      + by apply color_refine_good_hm; apply good_mark=> //; apply in_part_in_bnodes.
      + by move=> /=; rewrite finePn1.
    Qed.

    Lemma uniq_template (g : seq (triple I B L)) (ug: uniq g) : uniq (template g).
    Proof.
    rewrite /template; case: ifP=> H.
      rewrite sort_uniq; apply uniq_label_is_fine=> //.
      by move=> h; rewrite color_good_hm.
    apply uniq_distinguish=> //= ; rewrite ?H //. 
    - by apply: color_ubs; apply: init_hash_ubs.
    - by apply color_good_hm.
    Qed.

    Lemma mem_nilP (T : eqType) (s : seq T) : s =i [::] <-> s = [::].
    Proof.
    case: s=> [//| h tl]; split=> [mem|//].
    have := in_nil h.
    by rewrite -mem in_cons eqxx //.
    Qed.

    Lemma mem_eq_terms_ts (g h : seq (triple I B L)) :
      g =i h -> terms_ts g =i terms_ts h.
    Proof.
    move=> mem_eq t.
    suffices imp ts1 ts2:
      (forall (t : triple I B L), t \in ts1 -> t \in ts2) ->
        (forall (trm : term I B L), trm \in terms_ts ts1 -> trm \in terms_ts ts2).
      by apply /idP/idP; apply imp; move=> ?; rewrite -mem_eq.
    move=> /= {}mem_eq {}t; rewrite /terms_ts !mem_undup.
    move=> /flatten_mapP /=[t' t'ing tinterm].
    by apply /flatten_mapP=> /=; exists t'=> //; apply mem_eq.
    Qed.

    Lemma mem_eq_bnodes_ts (g h : seq (triple I B L)) :
      g =i h -> bnodes_ts g =i bnodes_ts h.
    Proof.
    move=> /mem_eq_terms_ts/= mem_eq b.
    by rewrite !mem_undup !mem_filter mem_eq.
    Qed.

    Lemma mem_eq_get_bts (g h : seq (triple I B L)) :
      g =i h -> get_bts g =i get_bts h.
    Proof.
    move=> /mem_eq_bnodes_ts/= mem_eq b.
    by apply eq_mem_pmap.
    Qed.

    Lemma piso_sort (g: seq (triple I B L)) (mu : B -> B) :
      is_pre_iso_ts g (sort le_triple (relabeling_seq_triple mu g)) mu
      <-> is_pre_iso_ts g (relabeling_seq_triple mu g) mu.
    Proof.
    rewrite /is_pre_iso_ts/bnode_map_bij !uniq_get_bts/=.
    split=> H.
    + apply uniq_perm.
      - by rewrite (perm_uniq H) uniq_get_bts.
      - by rewrite uniq_get_bts.
      - move=> b; rewrite (perm_mem H).
        by apply mem_eq_get_bts=> b'; rewrite mem_sort.
    + apply uniq_perm.
      - by rewrite (perm_uniq H) uniq_get_bts.
      - by rewrite uniq_get_bts.
      - move=> b; rewrite (perm_mem H).
        by apply mem_eq_get_bts=> b'; rewrite mem_sort.
    Qed.

    Lemma uniq_map_pre_iso (mu : B -> B) (ts : seq (triple I B L)) :
      uniq (map mu (get_bts ts)) ->
        is_pre_iso_ts ts (relabeling_seq_triple mu ts) mu.
    Proof.
    move=> umu; rewrite /is_pre_iso_ts/bnode_map_bij !uniq_get_bts /=.
    apply perm_eq_bts_relabel_inj_in; last by apply perm_refl.
    by apply /in_map_injP=> //; apply uniq_get_bts.
    Qed.

    Lemma piso_funof (g : seq (triple I B L)) (hm: hash_map) :
      bnodes_hm hm =i get_bts g ->
        is_fine (gen_partition hm) ->
          is_pre_iso_ts g (relabeling_seq_triple (fun_of_hash_map hm) g) (fun_of_hash_map hm).
    Proof.
    by move=> mem_eq fine; apply uniq_map_pre_iso; apply uniq_get_bts_is_fine.
    Qed.

    Lemma init_hash_nil : init_hash [::] = [::].
    Proof.
    move: (good_init [::]).
    case: (init_hash [::]) ; first by [].
    move=> [b n] l; rewrite /get_bts/==> contr.
    have := in_nil b.
    by rewrite -contr in_cons eqxx.
    Qed.

    Lemma color_nil_nil : color [::] [::] = [::].
    Proof.
    move: (color_good_hm [::] [::]).
    rewrite /get_bts/=.
    have /(_ B) H : [::] =i [::] by move=> b.
    move=> /(_ H){H}.
    case: (color [::] [::]) ; first by [].
    move=> [b n] l contr.
    have := in_nil b.
    by rewrite -contr in_cons eqxx.
    Qed.

    Lemma template_nil_nil : template [::] = [::].
    Proof.
    rewrite /template/=; case: ifP; first by [].
    by rewrite init_hash_nil color_nil_nil.
    Qed.


    Lemma foldl_default (gs : seq (seq (triple I B L))) (x0 x1: seq (triple I B L)):
        foldl choose_graph x0 gs = x1 ->
        (x0 == x1) = false ->
        forall (x2 : seq (triple I B L)),
          cmp x2 x0 ->
          foldl choose_graph x0 gs = foldl choose_graph x2 gs.
    Proof.
    elim: gs=> [/=->| hd tl IHtl] /=; first by rewrite eqxx.
    rewrite {2 4 6}/choose_graph.
    case_eq (x0 == hd); first by move=> /eqP <-; rewrite cmp_refl=> H F x2 ->.
    case: ifP.
    + by move=> cmp_x0hd neq_x0hd H F x2 cmp_x2x0; rewrite (cmp_trans cmp_x2x0 cmp_x0hd).
    move=> cmp_x0hdPn neq_x0hd foldl_eq neq_x0x1 x2 cmp_x2x0.
    case: ifP => [cmp_x2hd|cmp_x2hdPn]; last by apply IHtl.
    apply IHtl=> //.
    by move: (cmp_total hd x0); rewrite cmp_x0hdPn orbF=> ->.
    Qed.

    Lemma foldl_can_in_choose (l : seq (seq (triple I B L))) (x : seq (triple I B L)):
      (forall y : seq (triple I B L), y \in l -> cmp x y) ->
        foldl choose_graph x l = x -> (l == [::]) || (x \in l).
    Proof.
    elim: l x=> [//| hd t IHt] x cmp_in.
    rewrite /=; rewrite /choose_graph cmp_in; last by rewrite in_cons eqxx.
    suffices cmp_inW : forall y : seq (triple I B L), y \in t -> cmp x y.
      case_eq (hd == x); first by move=> /eqP ->; rewrite in_cons eqxx.
      move=> neq_hdx eq_fold.
      have cmpd : cmp x hd by apply cmp_in; rewrite in_cons eqxx.
      move: (distinguish_choice_default t hd)=> [].
      by move=> eqH; rewrite eqH in eq_fold; rewrite eq_fold eqxx // in neq_hdx.
      by rewrite eq_fold in_cons=> ->; rewrite orbT.
    by move=> y yin; apply cmp_in; rewrite in_cons yin orbT.
    Qed.

        (* This is where we use the fact that can is nil *)
    Lemma nil_is_nil (g : seq (triple I B L)) (hm : hash_map):
      bnodes_hm hm =i get_bts g ->
      (uniq (bnodes_hm hm)) ->
      ~~ is_fine (gen_partition hm) ->
      distinguish g hm = g0 -> g = g0.
    Proof.
    have : M hm < S (M hm) by apply ltnSn.
    move: hm (M hm).+1.
    move=> hm n; move: n hm=> n.
    elim: n => [//| n IHn hm measure mem_eq_bhm huniq neq_fine].
    rewrite distinguish_fold_map //.
    move=> /(foldl_can_in_choose _ _)/orP[]; first by move=> ?; rewrite can_extremum //.
    + by rewrite map_nil_is_nil choose_from_not_fine.
    rewrite /canonicalize; move=> /mapP[/= b bin].
    case: ifP=> [_|].
    + have ->: g0 = sort le_triple g0 by [].
      move=> /rdf_leP; rewrite perm_sym.
      by move=> /perm_nilP/eqP; rewrite map_nil_is_nil=> /eqP->.
    + move=> H /eqP; rewrite eq_sym=> /eqP.
      apply IHn=> //; last by rewrite H.
      + apply: Order.POrderTheory.le_lt_trans (color_refineP _ _) _.
       by apply: Order.POrderTheory.lt_le_trans (markP _ _ _ _ _) measure.
      + by apply color_refine_good_hm; apply good_mark=> //; apply in_part_in_bnodes.
      + apply: color_refine_ubs; apply: mark_ubs=> //; exact: in_part_in_bnodes.
    Qed.

    Lemma distinguish_piso (g : seq (triple I B L)) (ug: uniq g):
      ~~ is_fine (gen_partition (color g (init_hash g))) ->
        exists mu : B -> B,
          distinguish g (color g (init_hash g)) = sort le_triple (relabeling_seq_triple mu g)
          /\ is_pre_iso_ts g (distinguish g (color g (init_hash g))) mu.
    Proof.
    set hm := (color g (init_hash g)).
    have : uniq (bnodes_hm hm).
      by apply: color_ubs; apply: init_hash_ubs.
    have : M hm < S (M hm) by apply ltnSn.
    have : bnodes_hm hm =i get_bts g by apply color_good_hm; apply good_init.
    move: hm (M hm).+1.
    move=> hm n; move: n hm=> n.
    elim: n => [//| n IHn hm' ghm hmM] uniqP finePn.
    move: (distinguish_choice g hm')=> //= [] //.
    + move=> H; rewrite H; move/(nil_is_nil g _ ghm uniqP finePn) : H ->.
      by exists id; split; first by rewrite relabeling_seq_triple_id.
    + move=> /mapP/=[bn inp ->].
      case_eq  (is_fine (gen_partition (color_refine g (mark bn.1 hm'))))=> H.
      - exists (fun_of_hash_map (color_refine g (mark bn.1 hm'))).
        rewrite /canonicalize; split=> //; rewrite H //.
        apply piso_sort; apply piso_funof; last by apply H.
        apply color_refine_good_hm; apply good_mark=> //.
        by apply in_part_in_bnodes.
      - rewrite /canonicalize H; apply IHn=> //; last by rewrite H.
        + apply color_refine_good_hm; apply good_mark=> //.
          by apply in_part_in_bnodes.
        + eapply Order.POrderTheory.le_lt_trans; first by apply color_refineP.
          exact: (Order.POrderTheory.lt_le_trans (markP _ _ finePn uniqP inp) hmM).
        + apply: color_refine_ubs; apply: mark_ubs=> //; exact: in_part_in_bnodes.
    Qed.

    Lemma preiso_out_template (g : seq (triple I B L)) (ug : uniq g) :
      exists mu, (template g) = sort le_triple (relabeling_seq_triple mu g)
                 /\ is_pre_iso_ts g (template g) mu.
    Proof.
    move/eqP : (eq_refl (template g)).
    rewrite {2}/template.
    case: ifP=> is_fine ->.
    exists (fun_of_hash_map (color g (init_hash g))); split=> //.
    + apply piso_sort; apply piso_funof=> //.
      by apply color_good_hm; apply good_init.
    by apply distinguish_piso=> //; rewrite is_fine.
    Qed.

    Lemma eiso_sort (g: seq (triple I B L)) (mu : B -> B) :
      is_effective_iso_ts g (relabeling_seq_triple mu g) mu ->
      is_effective_iso_ts g (sort le_triple (relabeling_seq_triple mu g)) mu.
    Proof.
    move=> /and3P/= [piso urel peq].
    apply /and3P; split=> //; first by apply piso_sort.
    apply uniq_perm=> //; first by rewrite sort_uniq.
    by move=> b; rewrite mem_sort.
    Qed.

    Lemma eiso_out_template (g : seq (triple I B L)) (ug : uniq g) :
      effective_iso_ts g (template g).
    Proof.
    rewrite /iso_ts.
    move: (uniq_template g ug).
    suffices [mu  [-> piso utg]]:
      exists mu, (template g) = sort le_triple (relabeling_seq_triple mu g)
                 /\ is_pre_iso_ts g (template g) mu.
      rewrite sort_uniq in utg.
      exists mu; apply eiso_sort.
      have {}piso : is_pre_iso_ts g (relabeling_seq_triple mu g) mu by apply piso_sort.
      by move : (ts_pre_iso_effective_iso utg piso)=> eiso //.
    by apply preiso_out_template.
    Qed.

    Lemma simpl_fun_of_hm (hm : hash_map):
      uniq (bnodes_hm hm) ->
        {in (bnodes_hm hm),
         hm =1 (nat_inj \o (fun b : B => (nth 0 (map snd hm) (index b (bnodes_hm hm)))))}.
    Proof.
    move=> ubn b /bnodes_hm_has_eq_bnodes bin.
    rewrite /fun_of_hash_map.
    rewrite bnodes_hm_index_size; last by rewrite -has_eq_bnodes.
    by rewrite /= -(nth_map _ 0 snd) // bnodes_hm_index_ltn // - has_eq_bnodes.
    Qed.

    Lemma in_hm (hm : hash_map):
      uniq (bnodes_hm hm) ->
      {in hm,
            (fun (bn :B * nat) => (nth 0 [seq i.2 | i <- hm] (index bn.1 (bnodes_hm hm)))) =1 snd}.
    Proof.
    move=> /= ubs bn bnin.
    suffices -> : (index bn.1 (bnodes_hm hm)) = (index bn hm).
    by rewrite (nth_map bn) ?nth_index ?index_mem.
    apply index_map_in=> //.
    apply /in_map_injP=> //.
    by rewrite (hm_zip hm); apply zip_uniq_l.
    Qed.

    Lemma nth_hash (hm: hash_map):
      (uniq (bnodes_hm hm)) ->
      [seq nth 0 [seq i.2 | i <- hm] (index b (bnodes_hm hm)) | b <- bnodes_hm hm] = hashes_hm hm.
    Proof.
    elim: hm=> [//|hd tl IHtl] ubns.
    rewrite /= eqxx /=; congr cons.
    rewrite -IHtl; last by apply: uniq_tail ubns.
    apply eq_in_map => b bin.
    set i := index _ _.
    set s := map _ tl.
    suffices -> : hd.1 == b = false.
      by case: s.
    move: ubns=> /=/andP[/memPnC /(_ b bin)].
    by case: (hd.1 == b).
    Qed.

    Lemma peq_map_hm_bnodes (hm1 hm2: hash_map):
      uniq (bnodes_hm hm1) ->
      uniq (bnodes_hm hm2) ->
      (perm_eq (map hm1 (bnodes_hm hm1)) (map hm2 ((bnodes_hm hm2)))) ->
      (perm_eq (hashes_hm hm1) (hashes_hm hm2)).
    Proof.
    rewrite /fun_of_hash_map=> u1 u2.
    have /eq_in_map -> := simpl_fun_of_hm _ u1.
    have /eq_in_map -> := simpl_fun_of_hm _ u2.
    rewrite (map_comp nat_inj) (map_comp nat_inj _ (bnodes_hm hm2)) !nth_hash //.
    by apply perm_map_inj; apply nat_inj_.
    Qed.

    Lemma distinguish_perm_hm : forall (hm p : hash_map) g,
        (uniq (bnodes_hm hm)) ->
        ~~ is_fine (gen_partition hm) ->
        bnodes_hm hm =i get_bts g ->
        perm_eq hm p -> distinguish g hm = distinguish g p.
    Proof.
    move=> hm p g.
    move: p.
    have : M hm < S (M hm) by apply ltnSn.
    move: hm (M hm).+1.
    move=> hm n; move: n hm=> n.
    elim: n => [//| n' IHn hm] measure p ubs_hm is_fineN mem_eq peq.
    have is_fineN_p : ~~ is_fine (gen_partition p).
      by rewrite (perm_hash_eq_fine _ hm) //; apply: perm_map; rewrite perm_sym. 
    have ubs_p : uniq (bnodes_hm p).
      have : perm_eq (bnodes_hm p) (bnodes_hm hm) by apply: perm_map; rewrite perm_sym.
    by move/perm_uniq->.
    rewrite !distinguish_fold_map/distinguish_fold //.
    set cang := map _ _.
    set canh := map _ _.
    suffices eq_mem_ch : cang =i canh.
    by rewrite !foldl_idx/= (eq_big_idem _ _ choose_graph_idem eq_mem_ch).
    rewrite {}/cang{}/canh=>/= c.
    suffices peq_cp : perm_eq (choose_part hm) (choose_part p).
      rewrite -(eq_mem_map _ (perm_mem peq_cp)).
      suffices /eq_in_map -> : {in choose_part hm, canonicalize g hm =1 canonicalize g p} by [].
      move=> /= bn bnin.
      rewrite /canonicalize.
      have peq_cr :
        perm_eq (color_refine g (mark bn.1 hm)) (color_refine g (mark bn.1 p)).
        apply color_refine_perm_hm; apply mark_perm_hm=> //. 
        exact: in_part_in_bnodes.
      have /(perm_map snd)/perm_hash_eq_fine -> := peq_cr.
      case: ifP=> [fine| /negP/negP finePn].
      - apply /rdf_leP.
        suffices /relabeling_seq_triple_ext_in -> :
          {in get_bts g, (color_refine g (mark bn.1 hm)) =1 (color_refine g (mark bn.1 p))} by [].
        move=> b.
        rewrite -mem_eq=> bin.
        apply: fun_of_hash_perm.
        + suff : uniq (bnodes_hm (color_refine g (mark bn.1 hm))) by [].
          by apply color_refine_ubs; apply mark_ubs=> //; apply in_part_in_bnodes.
        + apply color_refine_perm_hm; apply mark_perm_hm=> //.
        exact: in_part_in_bnodes.
        + rewrite color_refine_good_hm; first by rewrite -mem_eq.
          by apply good_mark=> //; apply in_part_in_bnodes.
      - rewrite (IHn _ _ _ _ _ _ peq_cr) //.
        + eapply Order.POrderTheory.le_lt_trans; first by apply color_refineP.
          by apply (Order.POrderTheory.lt_le_trans (markP _ _ is_fineN ubs_hm bnin) measure).
        + apply color_refine_ubs.
          apply mark_ubs=> //.
          by apply in_part_in_bnodes.
        + rewrite (perm_hash_eq_fine _ (color_refine g (mark bn.1 p))) //. 
          by apply: perm_map.
        + move=> b; rewrite color_refine_good_hm //.
          apply good_mark=> //.
          by apply in_part_in_bnodes.
        + exact: choose_part_order.
         (* by apply perm_map. *)
    Qed.


    Lemma distinguish_perm_graph : forall (hm : hash_map) (g h : seq (triple I B L)),
        (uniq (bnodes_hm hm)) ->
        ~~ is_fine (gen_partition hm) ->
        bnodes_hm hm =i get_bts g ->
        perm_eq g h -> distinguish g hm = distinguish h hm.
    Proof.
    move=> hm g h.
    move: g.
    have : M hm < S (M hm) by apply ltnSn.
    move: hm (M hm).+1.
    move=> hm n; move: n hm=> n.
    elim: n => [//| n' IHn hm] measure g ubs_hm fineN_hm mem_eq peq.
    rewrite !distinguish_fold_map/distinguish_fold //.
    set cang := map _ _.
    set canh := map _ _.
    suffices eq_mem_ch : cang =i canh.
      by rewrite !foldl_idx/= (eq_big_idem _ _ choose_graph_idem eq_mem_ch).
    rewrite {}/cang{}/canh=>/= c.
    suffices /eq_in_map -> : {in choose_part hm, canonicalize g hm =1 canonicalize h hm} by [].
      move=> /= bn bnin.
      rewrite /canonicalize.
      have peq_cr :
        perm_eq (color_refine g (mark bn.1 hm)) (color_refine h (mark bn.1 hm)).
      by apply color_refine_perm_graph.
      have /(perm_map snd)/perm_hash_eq_fine -> := peq_cr.
      case: ifP=> [fine| finePn].
      - apply /rdf_leP.
        suffices /relabeling_seq_triple_ext_in -> :
          {in get_bts g, (color_refine g (mark bn.1 hm)) =1 (color_refine h (mark bn.1 hm))} by apply perm_map.
        move=> b.
        rewrite -mem_eq=> bin.
        apply fun_of_hash_perm.
        + suff : uniq (bnodes_hm (color_refine g (mark bn.1 hm))) by [].
          by apply color_refine_ubs; apply mark_ubs=> //; apply in_part_in_bnodes.
        + by apply color_refine_perm_graph.
        + rewrite color_refine_good_hm; first by rewrite -mem_eq.
          apply good_mark=> //.
          by apply in_part_in_bnodes.
      - rewrite -(IHn _ _ _ _ _ _ peq) //.
        + rewrite (distinguish_perm_hm _ _ g _ _ _ peq_cr) //.
          * apply color_refine_ubs; apply mark_ubs=> //.
            by apply in_part_in_bnodes.
          * rewrite (perm_hash_eq_fine _ (color_refine h (mark bn.1 hm))) ?finePn //. 
            by apply: perm_map.
            move=> b; rewrite color_refine_good_hm //.
        + move=> b'; rewrite (good_mark g) //.
          by apply in_part_in_bnodes.
        + eapply Order.POrderTheory.le_lt_trans; first by apply color_refineP.
          by apply (Order.POrderTheory.lt_le_trans (markP _ _ fineN_hm ubs_hm bnin) measure).
        + apply color_refine_ubs.
          apply mark_ubs=> //.
          by apply in_part_in_bnodes.
        + by rewrite finePn.
        + move=> b; rewrite color_refine_good_hm //.
        by apply perm_mem; apply peq_get_bts; rewrite perm_sym.
        apply good_mark=> //.
        by move=> b'; move/peq_get_bts/perm_mem : peq=> <-.
        by apply in_part_in_bnodes.
    Qed.

    Section wip.

      Definition post_rel (f : seq (triple I B L) -> hash_map -> hash_map) :=
        forall (G : seq (triple I B L)) (hm : hash_map) (mu : B -> B),
          {in (get_bts G)&, injective mu} ->
          {in (bnodes_hm hm)&, injective mu} ->
          perm_eq (f (relabeling_seq_triple mu G) (map1 mu hm)) (map1 mu (f G hm)).

      Definition perm_graph (f : seq (triple I B L) -> hash_map -> hash_map) :=
        forall (G H: seq (triple I B L)), perm_eq G H -> forall (hm : hash_map), perm_eq (f G hm) (f H hm).

      Definition perm_hm (f : seq (triple I B L) -> hash_map -> hash_map) :=
        forall (hm p : hash_map), perm_eq hm p -> forall (G : seq (triple I B L)), perm_eq (f G hm) (f G p).


      Lemma perm_graph_in_hm (f g : seq (triple I B L) -> hash_map -> hash_map):
        perm_hm f ->
        perm_graph g ->
        forall (G H : seq (triple I B L)),
          perm_eq G H ->
          forall (I : seq (triple I B L)) (hm : hash_map),
                 perm_eq (f I (g G hm)) (f I (g H hm)).
     Proof.
     move=> f_perm_hm g_perm_graph G H peq i hm.
     by apply f_perm_hm; apply g_perm_graph.
     Qed.

     Lemma post_rel_in_hm (f g : seq (triple I B L) -> hash_map -> hash_map):
        perm_hm f ->
        post_rel g ->
        forall (G H : seq (triple I B L)) (hm : hash_map) (mu : B -> B),
            {in (get_bts G)&, injective mu} ->
              {in (bnodes_hm hm)&, injective mu} ->
            perm_eq (f H (g (relabeling_seq_triple mu G) (map1 mu hm))) (f H (map1 mu (g G hm))).
     Proof.
     move=> f_perm_hm g_post_rel G H hm mu mu_injG mu_injhm.
     by apply f_perm_hm; apply g_post_rel.
     Qed.

     Lemma perm_post_rel_in_hm (f : seq (triple I B L) -> hash_map -> hash_map):
       perm_graph f ->
       post_rel f ->
       forall (G H : seq (triple I B L)) (mu: B -> B),
         perm_eq (relabeling_seq_triple mu G) H ->
         {in (get_bts G)&, injective mu} ->
         forall (hm : hash_map), {in (bnodes_hm hm)&, injective mu} ->
           perm_eq (f H (map1 mu hm)) (map1 mu (f G hm)).
     Proof.
     move=> f_perm_graph f_post_rel G H mu peq mu_injG hm mu_injHm.
     have step : perm_eq (f H (map1 mu hm)) (f (relabeling_seq_triple mu G) (map1 mu hm)).
       by apply f_perm_graph; rewrite perm_sym.
     apply: (perm_trans step).
     by apply f_post_rel.
     Qed.

     Lemma perm_graph_post_rel_in_hm (f g : seq (triple I B L) -> hash_map -> hash_map):
       perm_hm f ->
       perm_graph g ->
       post_rel g ->
       forall (G H : seq (triple I B L)) (mu: B -> B),
         perm_eq (relabeling_seq_triple mu G) H ->
           {in (get_bts G)&, injective mu} ->
             forall (hm : hash_map), {in (bnodes_hm hm)&, injective mu} ->
               perm_eq (f H (g H (map1 mu hm))) (f H (map1 mu (g G hm))).
     Proof.
     move=> f_perm_hm g_perm_graph g_post_rel G H mu peq mu_injG hm mu_injHm.
     by apply f_perm_hm; apply perm_post_rel_in_hm.
     Qed.

     Definition pres_bnodes (f : seq (triple I B L) -> hash_map -> hash_map) :=
       forall (G : seq (triple I B L))(hm : hash_map),
         bnodes_hm hm =i get_bts G -> bnodes_hm (f G hm) =i get_bts G.

     Lemma post_rel_graph_hm (f g : seq (triple I B L) -> hash_map -> hash_map):
       perm_hm f ->
       perm_graph f ->
       post_rel f ->
       perm_graph g ->
       post_rel g ->
       pres_bnodes g ->
       forall (G H : seq (triple I B L)) (mu: B -> B),
         perm_eq (relabeling_seq_triple mu G) H ->
           {in (get_bts G)&, injective mu} ->
             forall (hm : hash_map),
              bnodes_hm hm =i get_bts G ->
              perm_eq (f H (g H (map1 mu hm))) (map1 mu (f G (g G hm))).
     Proof.
     move=> f_perm_hm f_perm_graph f_post_rel g_perm_graph g_post_rel g_pres_bnodes G H mu peq mu_injG hm mem_eq.
     have /perm_trans -> // : perm_eq (f H (g H (map1 mu hm))) (f H (map1 mu (g G hm))).
       apply f_perm_hm; apply perm_post_rel_in_hm=> // b bin; rewrite !mem_eq; apply mu_injG.
     apply perm_post_rel_in_hm => //.
     move: g_pres_bnodes=> /(_ _ _ mem_eq) f_mem_eq.
     by move => b bin; rewrite !f_mem_eq; apply mu_injG.
     Qed.

    End wip.

    Definition init_hash' (g : seq (triple I B L)): hash_map -> hash_map :=
      fun hm => init_hash g.

    Lemma init_hash_shape (g : seq (triple I B L)) (hm : hash_map) :
      init_hash g = init_hash' g hm.
    Proof. by []. Qed.

    Lemma init_hash_post_rel : post_rel init_hash'.
    Proof.
    move=> G hm mu mu_injG mu_injhm.
    by rewrite -init_hash_shape perm_sym; apply init_hash_inj_rel.
    Qed.

    Lemma init_hash_is_perm_graph: perm_graph init_hash'.
    Proof.
    by move=> G H peq hm; rewrite -init_hash_shape; apply init_hash_perm_graph.
    Qed.

    Lemma init_hash_is_perm_hm: perm_hm init_hash'.
    by move=> hm p _ g; rewrite -init_hash_shape.
    Qed.

    Lemma color_post_rel : post_rel color.
    Proof.
    move=> G hm mu mu_injG mu_injhm.
    by apply color_post_relabeling.
    Qed.

    Lemma color_is_perm_graph: perm_graph color.
    Proof.
    by move=> G H peq hm; apply color_perm_graph.
    Qed.

    Lemma color_is_perm_hm: perm_hm color.
    by move=> hm p peq g; rewrite perm_sym; apply color_perm_hm.
    Qed.

    Lemma color_pres_bnodes : pres_bnodes color.
    Proof. by move=> G hm; apply color_good_hm. Qed.

    Hint Resolve init_hash_post_rel.
    Hint Resolve init_hash_is_perm_graph.
    Hint Resolve init_hash_is_perm_hm.
    Hint Resolve color_post_rel.
    Hint Resolve color_is_perm_graph.
    Hint Resolve color_is_perm_hm.
    Hint Resolve color_pres_bnodes.

    Lemma color_refine_post_rel : post_rel color_refine.
    Proof.
    move=> G hm mu mu_injG mu_injhm.
    by apply color_refine_post_relabeling.
    Qed.

    (* Lemma color_refine_is_perm_graph: perm_graph color_refine. *)
    (* Proof. *)
    (* by move=> G H peq hm; apply color_refine_perm_graph. *)
    (* Qed. *)

    (* Lemma color_refine_is_perm_hm: perm_hm color_refine. *)
    (* by move=> hm p peq g; rewrite perm_sym; apply color_refine_perm_hm. *)
    (* Qed. *)

    Lemma peq_get_bts (ts1 ts2: seq (triple I B L)): perm_eq ts1 ts2 -> perm_eq (get_bts ts1) (get_bts ts2).
    Proof.
    move=> peq; rewrite /get_bts/get_bs.
    by apply perm_pmap; apply peq_bnodes.
    Qed.

    Lemma eiso_correct_complete (g h : seq (triple I B L)) (ug: uniq g) (uh: uniq h) :
      effective_iso_ts g h <-> (template g) == (template h).
    Proof.
    split; last first.
    + move=> /eqP eqmgmh.
      have := eiso_out_template g ug.
      rewrite eqmgmh=> mgh.
      have /(effective_iso_ts_sym uh) hmh := eiso_out_template h uh.
      by apply: (effective_iso_ts_trans mgh hmh).
    rewrite /template=> eiso; rewrite -(iso_color_fine eiso) //.
    set col_g := color _ _.
    set col_h := color _ _.
    have col_h_ubs : uniq (bnodes_hm col_h).
    by apply color_ubs; apply init_hash_ubs.
    case: ifP=> [fineP|finePn].
    + apply /eqP/rdf_leP.
      apply uniq_perm.
      - by apply uniq_label_is_fine=> //; apply color_good_hm; apply good_init.
      - rewrite (iso_color_fine eiso) // in fineP.
        by apply uniq_label_is_fine=> //; apply color_good_hm; apply good_init.
        by apply iso_color_fine_can.
    +
      case: eiso=> mu /and3P[piso urel peq].
      have mu_inj := is_pre_iso_ts_inj piso.
      have peq_col : perm_eq col_h (map1 mu col_g).
        rewrite /col_h/col_g (init_hash_shape _ (map1 mu [::])) (init_hash_shape _ [::]).
        have /perm_trans -> // : (perm_eq (color h (init_hash' h (map1 mu [::]))) (color h (map1 mu (init_hash' g [::])))).
          by apply perm_graph_post_rel_in_hm.
        by apply perm_post_rel_in_hm=> // b bin; rewrite !good_init; apply mu_inj.
      have col_h_rel_mem_bs : bnodes_hm col_h =i get_bts (relabeling_seq_triple mu g).
        move=> b; rewrite color_good_hm; last by apply good_init.
        by apply perm_mem; apply peq_get_bts; rewrite perm_sym.
      have is_fineN_col_h : ~~ is_fine (gen_partition col_h).
        suff /perm_hash_eq_fine-> : perm_eq (hashes_hm col_h) (hashes_hm col_g) by rewrite finePn.
        rewrite -(hashes_of_map1 col_g mu).
        exact: perm_map.
      rewrite -(distinguish_perm_graph _ _ _ _ _ _ peq) // (distinguish_perm_hm _ _ _ _ _ _ peq_col) //.
      have : good_hash_map_for g col_g. by apply eq_mem_good_hm; apply color_hm_for.
      have : uniq (bnodes_hm col_g).
        by apply color_ubs; apply init_hash_ubs.
      have : M col_g < S (M col_g) by apply ltnSn.
      have : bnodes_hm col_g =i get_bts g by apply color_good_hm; apply good_init.
      move: col_g (M col_g).+1 {peq_col} finePn.
      move=> hm n; move: n hm=> n.
      elim: n => [//| n' IHn hm] hfine mem_eq_bs measure ubs_hm ghm_f.
      have huniq : uniq (bnodes_hm (map1 mu hm)).
         rewrite map1_bnodesC; apply/in_map_injP=> //.
         move=> b1 b2; rewrite !mem_eq_bs; exact: mu_inj.
      have hfine_mu : ~~ is_fine (gen_partition (map1 mu hm)).
         have := perm_refl (hashes_hm hm).
         rewrite -[in X in (perm_eq X  _)](hashes_of_map1 _ mu); move/perm_hash_eq_fine->.
         by rewrite hfine.
      rewrite !distinguish_fold_map /distinguish_fold ?hfine //.
      set cang := (map _ _).
      set canh := (map _ _).
      suffices mem_eq_cands : cang =i canh.
        by rewrite !foldl_idx (eq_big_idem _ _ choose_graph_idem mem_eq_cands) eqxx.
      rewrite /cang/canh.
      rewrite choose_part_post_relabeling.
      set pp := map1 _ _.
      rewrite map1_map -map_comp {}/pp.
      set can_g := canonicalize _ _.
      set can_h := canonicalize _ _.
      suffices -> :
        [seq can_g i | i <- choose_part hm] = [seq ((can_h) \o (fun p => (mu p.1, p.2))) i | i <-  choose_part hm] by [].
      suffices step (bn : B * nat) : bn \in choose_part hm -> can_g bn = can_h (mu bn.1, bn.2) by apply/eq_in_map.
        rewrite /can_g /can_h /canonicalize => hb /=.
        set hmg := (X in is_fine (gen_partition X)).
        set test_g := is_fine _.
        set hmh := (X in is_fine (gen_partition X)).
        set test_h := is_fine _.
        have -> : test_h = test_g.
         suffices /perm_hash_eq_fine : (perm_eq (hashes_hm hmg) (hashes_hm hmh)).
           by rewrite /test_g => ->.
         rewrite /hmh -(hashes_of_map1 hmg mu); apply perm_map.
         have /(perm_trans _) -> // : perm_eq (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm))) hmh.
           apply color_refine_perm_hm; apply mark_perm_hm=> //.
           rewrite map1_bnodesC map_f //; exact: in_part_in_bnodes.
         have /(perm_trans _) -> //: perm_eq (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm))) (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm))).
           apply color_refine_perm_hm; rewrite perm_sym.
           have H := in_part_in_bnodes _ _ hb.
           by apply (mark_post_rel _ _ H)=> b1 b2; rewrite !mem_eq_bs; apply mu_inj.
         have mu_inj_mhm: {in bnodes_hm (mark bn.1 hm) &, injective mu}.
           by move=> b1 b2; rewrite !(good_mark g) // ?in_part_in_bnodes //; apply mu_inj.
         by rewrite /hmg perm_sym; apply color_refine_post_rel=> //.
        case: ifP => [htest | hNtest].
        have ubs_hmg : (uniq (bnodes_hm hmg)).
            apply color_refine_ubs.
            apply mark_ubs=> //.
            by apply in_part_in_bnodes.
        have hmg_inj : {in get_bts g &, injective (color_refine g (mark bn.1 hm))}.
            move=> b1 b2 bin1 bin2.
          have eq_bs: (bnodes_hm (color_refine g (mark bn.1 hm))) =i get_bts g.
            by apply color_refine_good_hm; apply good_mark; [apply mem_eq_bs | apply in_part_in_bnodes].
          have hm_inj := funof_snd_inj _ _ eq_bs htest.
          rewrite !simpl_fun_of_hm ?eq_bs //.
          rewrite -/hmg.
          move=> /nat_inj_.
          have -> : b1 = (b1,nth 0 [seq i.2 | i <- hmg] (index b1 (bnodes_hm hmg))).1 by [].
          have -> : b2 = (b2,nth 0 [seq i.2 | i <- hmg] (index b2 (bnodes_hm hmg))).1 by [].
          suffices SU : forall (T U : eqType)(hm : seq (T * U)), uniq hm -> forall (t : T), t \in map fst hm ->
                                                                                                  forall (u : U),
                                                                                                    (t,(nth u (map snd hm) (index t (map fst hm)))) \in hm.
          have H: (b1, nth 0 [seq i.2 | i <- hmg] (index b1 (bnodes_hm hmg))) \in hmg.
            apply SU; last by rewrite eq_bs.
            by rewrite (hm_zip hmg); apply zip_uniq_l.
          have H2: (b2, nth 0 [seq i.2 | i <- hmg] (index b2 (bnodes_hm hmg))) \in hmg.
            apply SU; last by rewrite eq_bs.
            by rewrite (hm_zip hmg); apply zip_uniq_l.
          rewrite !in_hm //.
          by move=> /(hm_inj)=> /(_ H H2) [->].
          move=> T U tus utus t tin u.
          move: tin utus.
          elim: tus=> [//| [b' n''] tl IHtl] /=.
          rewrite in_cons=> /orP[].
          by move=> /eqP ->; rewrite eqxx /= in_cons eqxx.
          case_eq (b' == t).
          + by move=> /eqP ->; rewrite /= in_cons eqxx.
          + move=> H tin /andP[nin utl]; rewrite in_cons.
            suffices -> : ((t, nth u (n'' :: [seq i.2 | i <- tl]) (index t [seq i.1 | i <- tl]).+1) \in tl).
              by rewrite orbT.
            by apply IHtl=> //.
        - apply /rdf_leP.
          have in_hm_inj : {in bnodes_hm hm &, injective mu}.
            by move=> b1 b2; rewrite !mem_eq_bs; apply mu_inj.
          apply uniq_perm.
          rewrite /test_g/hmg in htest.
          apply /in_map_injP=> //.
          by apply inj_get_bts_inj_ts.
        - set cr := color_refine _ _.
          suffices : forall (hm p : hash_map),
                uniq (bnodes_hm hm) ->
                perm_eq hm p ->
                {in (bnodes_hm hm), fun_of_hash_map hm =1 p}.
            have ubs_cr : uniq (bnodes_hm cr).
              have /eq_map eq_mapC : fst \o (fun p : B * nat => (mu p.1,p.2)) =1 mu \o fst.
                by [].
              have mu_inj_hm: {in [seq i.1 | i <- hm] &, injective mu}.
                move=> b1 b2; rewrite !mem_eq_bs.
                by apply mu_inj.
              apply color_refine_ubs; apply mark_ubs.
              rewrite map1_map /bnodes_hm -map_comp.
              rewrite eq_mapC map_comp.
              rewrite map_inj_in_uniq //.
              rewrite map1_map/bnodes_hm -map_comp eq_mapC map_comp.
              by move/in_part_in_bnodes : hb=> /(map_f mu).
            have peq_cr: perm_eq cr (map1 mu (color_refine g (mark bn.1 hm))).
              rewrite /cr.
              have /(perm_trans) -> // : perm_eq (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm))) (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm))).
                apply color_refine_perm_hm.
                have H := in_part_in_bnodes _ _ hb.
                by apply (mark_post_rel _ _ H)=> b1 b2; rewrite !mem_eq_bs; apply mu_inj.
              apply color_refine_post_rel=> //.
              move=> b1 b2.
              rewrite !(good_mark g) //. apply mu_inj.
              by apply in_part_in_bnodes.
              by apply in_part_in_bnodes.
            move=> /(_ _ _ ubs_cr peq_cr) eq_hm.
            apply /in_map_injP=> //.
            apply inj_get_bts_inj_ts.
            move=> b1 b2 bin1 bin2.
            rewrite /cr !eq_hm.
            suffices /andP[/mapP /=[bb1 bb1in ->] /mapP/= [bb2 bb2in ->]]: (b1 \in (map mu (get_bts g))) && (b2 \in (map mu (get_bts g))).
            have -> : map1 mu (color_refine g (mark bn.1 hm)) (mu bb1) = (map1 mu (color_refine g (mark bn.1 hm)) \o mu) bb1 by [].
            have -> : map1 mu (color_refine g (mark bn.1 hm)) (mu bb2) = (map1 mu (color_refine g (mark bn.1 hm)) \o mu) bb2 by [].
            have ghm : good_hash_map_for g hmg.
              apply eq_mem_good_hm=> t; rewrite /hmg; apply color_refine_good_hm.
              by apply good_mark; [apply mem_eq_bs | apply in_part_in_bnodes].
            rewrite !ghm //.
            by move /hmg_inj=> /(_ bb1in bb2in) ->.
            have := perm_refl (relabeling_seq_triple mu g).
            move=> /peq_get_bts.
            move=> /perm_eq_bts_relabel_inj_in=> /(_ mu_inj) peq_rel.
            by rewrite !(perm_mem peq_rel); apply /andP; split.
          rewrite color_refine_good_hm //.
          have H := in_part_in_bnodes _ _ hb.
          have /perm_mem peq_mark:= mark_post_rel bn.1 hm H in_hm_inj.
          move=> b. rewrite (eq_mem_map _ peq_mark).
          rewrite map1_map -map_comp.
          have := perm_refl (relabeling_seq_triple mu g).
          move=> /peq_get_bts.
          move=> /perm_eq_bts_relabel_inj_in=> /(_ mu_inj) peq_rel.
          rewrite -(perm_mem peq_rel).
          have eq_bs_mark: (bnodes_hm (mark bn.1 hm)) =i get_bts g. by apply good_mark=> //; apply in_part_in_bnodes.
          rewrite -(eq_mem_map _ eq_bs_mark) /bnodes_hm -map_comp.
          by congr (in_mem b).
          *
          rewrite color_refine_good_hm //.
          have H := in_part_in_bnodes _ _ hb.
          have /perm_mem peq_mark:= mark_post_rel bn.1 hm H in_hm_inj.
          move=> b. rewrite (eq_mem_map _ peq_mark).
          rewrite map1_map -map_comp.
          have := perm_refl (relabeling_seq_triple mu g).
          move=> /peq_get_bts.
          move=> /perm_eq_bts_relabel_inj_in=> /(_ mu_inj) peq_rel.
          rewrite -(perm_mem peq_rel).
          have eq_bs_mark: (bnodes_hm (mark bn.1 hm)) =i get_bts g.
            by apply good_mark=> //; apply in_part_in_bnodes.
          rewrite -(eq_mem_map _ eq_bs_mark) /bnodes_hm -map_comp.
          by congr (in_mem b).
          by apply fun_of_hash_perm.
          ++
            rewrite relabeling_seq_triple_comp.
            apply relabeling_ext_in.
            apply eq_in_bs_ing.
            have: perm_eq (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm))) (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm))).
            have H := in_part_in_bnodes _ _ hb.
            by apply color_refine_perm_hm; apply (mark_post_rel _ _ H) ; move=> b1 b2; rewrite !mem_eq_bs; apply mu_inj.
            move=> peq' b1 b1in.
            have eq_bs_cr : bnodes_hm (color_refine g (mark bn.1 hm)) =i get_bts g.
              by apply color_refine_good_hm; apply good_mark=> //; apply in_part_in_bnodes.
            rewrite /=.
            suffices peq_cr : perm_eq (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm))) (map1 mu (color_refine g (mark bn.1 hm))).
              rewrite (fun_of_hash_perm _ _ _ peq_cr).
              have -> : map1 mu (color_refine g (mark bn.1 hm)) (mu b1) = (map1 mu (color_refine g (mark bn.1 hm)) \o mu) b1 by [].
              by rewrite (@eq_mem_good_hm g (color_refine g (mark bn.1 hm)) _).
            rewrite /bnodes_hm.
            move: peq_cr=> /(perm_map fst)/perm_uniq ->.
            have /eq_map eq_mapC : fst \o (fun p : B * nat => (mu p.1,p.2)) =1 mu \o fst by [].
            rewrite map1_map -map_comp eq_mapC map_comp.
            apply /in_map_injP.
            apply color_refine_ubs. apply mark_ubs. done. by apply in_part_in_bnodes.
            move=> b1' b2'. rewrite !eq_bs_cr. apply mu_inj.
            rewrite (eq_mem_map _ (perm_mem peq_cr)) map1_map -map_comp.
            have /eq_map eq_mapC : fst \o (fun p : B * nat => (mu p.1,p.2)) =1 mu \o fst.
                by [].
            rewrite eq_mapC.
            rewrite map_comp.
            move: b1in.
            rewrite -eq_bs_cr.
            by move=> /(map_f mu).
            have /perm_trans -> //: perm_eq (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm)))
                     (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm))).
              have H := in_part_in_bnodes _ _ hb.
              by apply color_refine_perm_hm; apply (mark_post_rel _ _ H) => //.
            apply color_refine_post_relabeling=> //.
              move=> b1' b2'.
              suffices mem_bs_mark : (bnodes_hm (mark bn.1 hm)) =i bnodes_hm hm.
                by rewrite !mem_bs_mark; apply in_hm_inj.
              move=> bb; rewrite (good_mark g) ?mem_eq_bs //.
              by rewrite -mem_eq_bs; apply in_part_in_bnodes.
        - set hh := mark _ _.
          have peq_mark_post_rel : perm_eq (mark (mu bn.1) (map1 mu hm)) (map1 mu (mark bn.1 hm)).
            have H := in_part_in_bnodes _ _ hb.
            by apply (mark_post_rel _ _ H) => b1 b2; rewrite !mem_eq_bs; apply mu_inj.
          have /(color_refine_perm_hm (relabeling_seq_triple mu g)) := peq_mark_post_rel.
          have cr_ubs : uniq (bnodes_hm (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm)))).
            apply color_refine_ubs. apply mark_ubs.
            rewrite map1_map/bnodes_hm -map_comp.
            have /eq_map eq_mapC : fst \o (fun p : B * nat => (mu p.1,p.2)) =1 mu \o fst.
              by [].
            rewrite eq_mapC map_comp.
            apply /in_map_injP=> //.
            have mu_inj_hm: {in [seq i.1 | i <- hm] &, injective mu}.
                move=> b1 b2; rewrite !mem_eq_bs.
                by apply mu_inj.
            by [].
            have /eq_map eq_mapC : fst \o (fun p : B * nat => (mu p.1,p.2)) =1 mu \o fst.
              by [].
            rewrite map1_map/bnodes_hm -map_comp eq_mapC map_comp.
            by move/in_part_in_bnodes/(map_f mu) : hb.
          have cr_mem_eq_bs : bnodes_hm (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm)))
                 =i get_bts (relabeling_seq_triple mu g).
            move=> b; rewrite color_refine_good_hm //.
            move=> b'; rewrite (good_mark (relabeling_seq_triple mu g)) //.
            rewrite map1_map/bnodes_hm -map_comp.
            have /eq_map eq_mapC : fst \o (fun p : B * nat => (mu p.1,p.2)) =1 mu \o fst.
              by [].
            rewrite eq_mapC map_comp=> b''.
            have /peq_get_bts/(perm_eq_bts_relabel_inj_in mu_inj) := perm_refl (relabeling_seq_triple mu g).
            move=> /perm_mem <-.
            by apply eq_mem_map.
            rewrite map1_map/bnodes_hm -map_comp.
            have /eq_map eq_mapC : fst \o (fun p : B * nat => (mu p.1,p.2)) =1 mu \o fst.
              by [].
            rewrite eq_mapC map_comp.
            by move/in_part_in_bnodes/(map_f mu) : hb.
            have side1 : ~~ is_fine (gen_partition (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm)))).
            suff/perm_hash_eq_fine-> : perm_eq (hashes_hm hmh) (hashes_hm hmg) by rewrite -/test_g hNtest.
            rewrite -(hashes_of_map1 hmg mu).
            apply: perm_map.
            have trans_l : perm_eq hmh (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm))). 
              apply: color_refine_perm_hm; apply: mark_post_rel; first by apply in_part_in_bnodes.
              move=> b1 b2. rewrite !mem_eq_bs. exact: mu_inj.
            apply: (perm_trans trans_l).
            apply: color_refine_post_rel => //. 
            move=> b1 b2. rewrite !(good_mark g) ?in_part_in_bnodes //; exact: mu_inj.
          move=> /(distinguish_perm_hm _ _ _) -> //.
          have peq_cr_post_rel : perm_eq (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm))) (map1 mu (color_refine g (mark bn.1 hm))).
            by apply color_refine_post_rel=> // b1 b2; rewrite !(good_mark g) // ?in_part_in_bnodes //; apply mu_inj.
          have cr_post_ubs : uniq (bnodes_hm (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm)))).
            move: peq_mark_post_rel. move=> /(color_refine_perm_hm (relabeling_seq_triple mu g)).
            by move=> /(perm_map fst) /perm_uniq <-.
          have cr_post_eq_mem : bnodes_hm (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm))) =i get_bts (relabeling_seq_triple mu g).
            move=> b; move: peq_mark_post_rel. move=> /(color_refine_perm_hm (relabeling_seq_triple mu g)).
            by move=> /(perm_map fst)/perm_mem <-.
          have side2 : ~~ is_fine (gen_partition (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm)))).
           suff/(perm_map snd)/perm_hash_eq_fine<- : perm_eq hmh (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm))) by []. 
           by apply: color_refine_perm_hm=> //.
          have /(distinguish_perm_hm _ _ _) -> // := peq_cr_post_rel.
          apply /eqP.
          apply IHn=> //.
          - apply color_refine_good_hm.
            by apply good_mark; last by apply in_part_in_bnodes.
          - eapply Order.POrderTheory.le_lt_trans; first by apply color_refineP.
            have {hfine} hfine : ~~ is_fine (gen_partition hm) by rewrite hfine.
            by apply (Order.POrderTheory.lt_le_trans (markP _ hm hfine ubs_hm hb) measure).
          - apply color_refine_ubs.
          apply mark_ubs=> //.
          by apply in_part_in_bnodes.
          apply (@eq_mem_good_hm g (color_refine g (mark bn.1 hm))).
          by apply color_refine_good_hm; apply good_mark; [ | apply in_part_in_bnodes].
     Qed.

    Lemma eiso_correct_complete' (g h : seq (triple I B L)) (ug: uniq g) (uh: uniq h) :
      perm_eq (template g) (template h) <-> effective_iso_ts g h.
    Proof.
    split; last by move=> /(eiso_correct_complete _ _ ug uh)/eqP ->; apply perm_refl.
    + move=> eqmgmh.
    have gmg := eiso_out_template g ug.
    suffices mgmh : effective_iso_ts (template g) (template h).
      have /(effective_iso_ts_sym uh) hmh := eiso_out_template h uh.
      apply: (effective_iso_ts_trans gmg _).
      by apply: (effective_iso_ts_trans mgmh hmh).
    have [mu [eiso _]]:= eqiso_ts (uniq_template _ ug) eqmgmh.
    by exists mu.
    Qed.

    Definition template_rdf (g : rdf_graph I B L) :=
      mkRdfGraph (uniq_template _ (ugraph g)).

    Lemma template_isocan : (@effective_isocanonical_mapping I B L template_rdf).
    Proof.
    split; first by move=> [g ug]; apply eiso_out_template.
    by move=> [g ug] [h uh]; apply eiso_correct_complete'.
    Qed.

  End Distinguish.
(* 
  Variable disp : Order.disp_t.
  (* TODO : check that order is needed, since below comes a comparison comp on graphs *)
  Variable I B L : orderType disp.
  Notation le_triple := (@le_triple disp I B L).


  (* Enumeration of b-nodes *)
  Hypothesis nat_inj : nat -> B.
  Hypothesis nat_inj_ : injective nat_inj. *)
  (* Definition template_isocan_ := @template_isocan disp I B L nat_inj nat_inj_
    (@le_st disp I B L) (@le_st_anti disp I B L) (@le_st_total disp I B L) (@le_st_trans disp I B L)
    nil isT erefl erefl (@nil_minimum disp I B L). *)


End Template.

Section KmappingInstance.  

Variable disp : Order.disp_t.
(* TODO : check that order is needed, since below comes a comparison comp on graphs *)
Variable I B L : orderType disp.
Notation le_triple := (@le_triple disp I B L).

Variable b_default : B.  

(* Enumeration of b-nodes *)
Hypothesis nat_inj : nat -> B.
Hypothesis nat_inj_ : injective nat_inj.

(* comparison on graphs, morally an order relation. *)

Variable (cmp : seq (triple I B L) -> seq (triple I B L) -> bool).

Hypothesis cmp_anti : antisymmetric cmp.
Hypothesis cmp_total : total cmp.
Hypothesis cmp_trans : transitive cmp.

(* A default graph *)
Let g0 := (@g0 disp I B L).

(* Determines a choice of default graph can *)
Hypothesis can_extremum : forall (x : seq (triple I B L)), cmp g0 x.

Let choose_graph := (@choose_graph disp I B L cmp).
Let choose_graphA := (@choose_graphA disp I B L cmp cmp_anti cmp_total cmp_trans).
Let choose_graphC := (@choose_graphC disp I B L cmp cmp_anti cmp_total).
Let can_lid := (@can_lid disp I B L cmp can_extremum).

HB.instance Definition _ :=
  Monoid.isComLaw.Build
    (seq (triple I B L)) g0
    choose_graph choose_graphA
    choose_graphC
    can_lid.

Local Notation hash_map := (@hash_map B).
Local Notation part := (@part B).
Local Notation partition := (@partition B).
Local Notation index_bnodes := (@index_bnodes disp B).

Arguments eq_hash {B} _ _.
Arguments eq_bnode {B} _ _.

Let fun_of_hash_map := (@fun_of_hash_map disp B nat_inj).
Let good_hash_map_for := (@good_hash_map_for disp I B L nat_inj).
(* Let init_hash_kmap := (@init_hash_kmap disp I B L). *)

Coercion fun_of_hash_map : hash_map >-> Funclass.

(* Initial hash map from a graph *)
Definition init_hash_kmap (ts : seq (triple I B L)) : hash_map :=
  let bs := get_bts ts in
  zip bs (nseq (size bs) 0).

(* init_hash g has the same bnodes as the graph g *)
Lemma good_init_kmap (g : seq (triple I B L)) : bnodes_hm (init_hash_kmap g) =i get_bts g.
Proof. by move=> x; rewrite /init_hash_kmap/bnodes_hm zip_proj1 // size_nseq. Qed.

(* the relabeling under injective functions "commutes" with init_hash modulo permutation *)
Lemma init_hash_inj_rel_kmap :
forall (g : seq (triple I B L)) (mu : B -> B),
  {in get_bts g &, injective mu} ->
  perm_eq (map1 mu (init_hash_kmap g)) (init_hash_kmap (relabeling_seq_triple mu g)).
Proof.
move=> g mu mu_inj.
rewrite /init_hash_kmap.
have eq_size : size (get_bts g) = size (nseq (size (get_bts g)) 0) by rewrite size_nseq.
rewrite map1_zip //.
have eq_num_bs: size (get_bts g) = size (get_bts (relabeling_seq_triple mu g)).
by apply size_rel_inj.
rewrite -eq_num_bs; apply perm_eq_zip_eql.
by rewrite -eq_num_bs size_map.
by rewrite size_map -eq_size.
apply constant_nseq.
apply perm_eq_bts_relabel_inj_in=> //.
Qed.

(* permutation equal graphs yield permutation equal hashmaps under init_hash *)
Lemma init_hash_perm_graph_kmap : forall g h : seq (triple I B L), perm_eq g h -> perm_eq (init_hash_kmap g) (init_hash_kmap h).
Proof.
move=> g h peq.
rewrite /init_hash_kmap.
have /peq_get_bts/perm_size eq_size := peq.
rewrite eq_size.
apply perm_eq_zip_eql=> //.
by rewrite size_nseq eq_size.
apply constant_nseq.
by apply peq_get_bts.
Qed.

(* the result of init_hash has uniq blank nodes *)
Lemma init_hash_ubs_kmap : forall g : seq (triple I B L), uniq (bnodes_hm (init_hash_kmap g)).
Proof.
move=> g; rewrite /init_hash_kmap/bnodes_hm.
by rewrite map_fst_zip_size ?uniq_get_bts // size_nseq.
Qed.

(* init hash yields a good hash for its input *)
(* TODO not longer necesary *)
(* Lemma init_hash_inv_kmap (g : seq (triple I B L)) : good_hash_map_for g (init_hash_kmap g). *)
(* Proof. *)
(* set s := get_bts g. *)
(* move=> mu mu_inj b bin. *)
(* rewrite /init_hash_kmap -/s. *)
(* set t : hash_map := zip _ _. rewrite /=. *)
(* by apply shift_hm=> //; rewrite /t /bnodes_hm zip_proj1 // size_nseq. *)
(* Qed. *)

(* Assia: This could even be the definition of gen_partition. *)
Definition gen_ordered_partition (hm : hash_map) : partition :=
  map (part_of hm) (sort leq (undup (hashes_hm hm))).

Lemma gen_ordered_partition_perm_eq hm :
  perm_eq (gen_ordered_partition hm) (gen_partition hm).
Proof.  by apply: perm_map; rewrite perm_sort. Qed.

(* Now the kmapping specific definitions: choose_part_kmap
   picks the non-trivial part with the least hash in the partition.
   Outputs the empty list when the partition does not have a
   non-singleton part (i.e., it is fine or empty) *)
Definition choose_part_kmap (hm : hash_map) : part :=
  head [::] (filter [pred x | size x > 1] (gen_ordered_partition hm)).

Definition color_kmap : seq (triple I B L) -> hash_map -> hash_map := 
  fun _ hm=> hm.
Definition color_refine_kmap : seq (triple I B L) -> hash_map -> hash_map := 
  fun _ hm=> hm.

Definition mark_hash_kmap_2 (b : B) (n : nat) (hm : hash_map) :=
  set_nth (b,n) hm (find (eq_bnode b) hm) (b,n).

Definition fresh (hm : hash_map) : nat :=
  (foldl maxn 0 (hashes_hm hm)).+1.

Definition M_kmap (hm :hash_map) : nat :=
  (size hm) - (distinguished hm).

(* Definition mark_kmap (b : B) (hm : hash_map) := *)
(*   mark_hash_kmap b (fresh hm) hm. *)

Definition mark_kmap_2 (b : B) (hm : hash_map) :=
  mark_hash_kmap_2 b (fresh hm) hm.


Lemma in_part_in_bnodes_kmap (bn : B * nat) (hm : hash_map):
    bn \in choose_part_kmap hm -> bn \in hm.
Proof.
rewrite /choose_part_kmap.
case/head_seq_seq_in=> // [] [] t [].
rewrite mem_filter; case/andP=> _ /mapP[] n.
rewrite mem_sort mem_undup => hn -> {t}.
(* x \in part_of hm k -> x \in hm should be a lemma ... *)
by rewrite mem_filter; case/andP.
Qed.

Lemma color_good_hm_kmap (g : seq (triple I B L)) (hm : hash_map):
    bnodes_hm hm =i get_bts g -> bnodes_hm (color_kmap g hm) =i get_bts g.
Proof. by []. Qed.

(* TODO not longer necesary *)
(* Lemma color_inv_kmap : forall (g : seq (triple I B L)) (hm : hash_map), *)
(*             good_hash_map_for g hm -> good_hash_map_for g (color_kmap g hm). *)
(* Proof. move=> g hm H1 mu ghf b bin; by apply H1. Qed. *)

Lemma color_post_relabeling_kmap : forall (g : seq (triple I B L)) (mu : B -> B) (hm : hash_map),
                        {in get_bts g &, injective mu} ->
                        {in bnodes_hm hm &, injective mu} ->
                        perm_eq (color_kmap (relabeling_seq_triple mu g) (map1 mu hm)) (map1 mu (color_kmap g hm)).
Proof. move=> g mu hm mu_inj_bs mu_inj_hm; by apply perm_refl. Qed.

Lemma color_perm_graph_kmap :
  forall (g h : seq (triple I B L)) (hm : hash_map), perm_eq g h -> perm_eq (color_kmap g hm) (color_kmap h hm).
Proof. by move=> g h hm peq; apply perm_refl. Qed.

Lemma color_refine_perm_graph_kmap :
  forall (g h : seq (triple I B L)) (hm : hash_map), perm_eq g h -> perm_eq (color_refine_kmap g hm) (color_refine_kmap h hm).
Proof. by apply color_perm_graph_kmap. Qed.

Lemma color_perm_hm_kmap :
  forall hm p : hash_map,
    perm_eq p hm ->
    forall g : seq (triple I B L), perm_eq (color_kmap g hm) (color_kmap g p).
Proof. by move=> hm p peq g; rewrite perm_sym. Qed.

Lemma color_refine_perm_hm_kmap :
  forall (g : seq (triple I B L)) (hm p : hash_map),
    perm_eq hm p ->
    perm_eq (color_refine_kmap g hm) (color_refine_kmap g p).
Proof. by move=> g hm p peq. Qed.

Lemma color_ubs_kmap :
  forall (hm : hash_map) (g : seq (triple I B L)),
    uniq (bnodes_hm hm) -> uniq (bnodes_hm (color_kmap g hm)).
Proof. by move=> hm g ubs. Qed.

Lemma color_refine_ubs_kmap :
  forall (hm : hash_map) (g : seq (triple I B L)),
    uniq (bnodes_hm hm) -> uniq (bnodes_hm (color_refine_kmap g hm)).
Proof. by apply color_ubs_kmap. Qed.

Lemma color_refine_good_hm_kmap : forall (g : seq (triple I B L)) (hm : hash_map),
                        bnodes_hm hm =i get_bts g -> bnodes_hm (color_refine_kmap g hm) =i get_bts g.
Proof. by apply color_good_hm_kmap. Qed.

(* TODO not longer necesary *)
(* Lemma color_refine_inv_kmap : forall (g : seq (triple I B L)) (hm : hash_map), *)
(*                     good_hash_map_for g hm -> good_hash_map_for g (color_refine_kmap g hm). *)
(* Proof. by apply color_inv_kmap. Qed. *)

Lemma color_refine_post_relabeling_kmap : forall (g : seq (triple I B L)) (hm : hash_map) (mu : B -> B),
                                {in get_bts g &, injective mu} ->
                                {in bnodes_hm hm &, injective mu} ->
                                perm_eq (color_refine_kmap (relabeling_seq_triple mu g) (map1 mu hm))
                                  (map1 mu (color_refine_kmap g hm)).
Proof. by move=> g hm mu ? ? ; apply color_post_relabeling_kmap. Qed.

Lemma mark_hash_kmap_bnodes (hm : hash_map) :
  forall (b : B) (n : nat),
  b \in bnodes_hm hm ->
  bnodes_hm (mark_hash_kmap_2 b n hm) = bnodes_hm hm.
Proof.
move=> b n.
rewrite /mark_hash_kmap_2.
rewrite set_nthE.
rewrite (hm_zip hm).
set hm' := zip _ _.
rewrite find_index_eq_bnode; last by apply size_proj.
rewrite -index_mem size_map /bnodes_hm.
have eq_size_proj : size [seq i.1 | i <- hm] = size [seq i.2 | i <- hm].
  by rewrite size_proj.
rewrite zip_proj1 // {1}/hm' size_zip eq_size_proj minn_refl.
move=> b_in; rewrite b_in.
rewrite /= {}/hm' -(hm_zip hm).
move: b_in {eq_size_proj}.
elim: hm=> [//| hd tl IHtl] /=.
case_eq (hd.1 == b).
by move=> /eqP ->; rewrite /= eqxx /= drop0.
by move=> -> /==> /IHtl ->.
Qed.

Lemma good_mark_kmap (g : seq (triple I B L)) (hm : hash_map):
  bnodes_hm hm =i get_bts g ->
    forall b : B, b \in bnodes_hm hm -> bnodes_hm (mark_kmap_2 b hm) =i get_bts g.
Proof.
move=> mem_eq b bin.
by rewrite mark_hash_kmap_bnodes //; apply mem_eq.
Qed.

Lemma mark_size (b : B) (hm : hash_map) :
  b \in (bnodes_hm hm) ->
  size (mark_kmap_2 b hm) = size hm.
Proof.
rewrite /mark_kmap_2/mark_hash_kmap_2.
elim: hm (fresh hm)=> [//| hd tl IHtl] n.
rewrite /= /mark_kmap_2/mark_hash_kmap_2; case: ifP=> [//|].
rewrite in_cons /eq_bnode/pred_eq/pred1 eq_sym/==> -> /= in_tl.
by rewrite IHtl.
Qed.

Lemma part_of_in_gen_part (hm : hash_map) (n : nat) :
  n \in hashes_hm hm -> part_of hm n \in gen_partition hm.
Proof. by move=> hn; apply/mapP; exists n => //; rewrite mem_undup. Qed.

Lemma part_of_in_gen_ord_part (hm : hash_map) (n : nat) :
  n \in hashes_hm hm -> part_of hm n \in gen_ordered_partition hm.
Proof.
move/(part_of_in_gen_part hm) => hn. 
by rewrite (perm_mem (gen_ordered_partition_perm_eq hm)).
Qed.

Lemma not_fine_chosen_part_in_P (hm : hash_map):
    ~~ is_fine (gen_partition hm) -> choose_part_kmap hm \in gen_partition hm.
Proof.
move=> h; apply/eqP/eqP.
rewrite /choose_part_kmap; set s := (X in head _ X).
case e: s => [ | hd tl] //=.
- suff: s != [::] by rewrite e.
  rewrite /s -has_filter. 
  rewrite (perm_has _ (gen_ordered_partition_perm_eq hm)).
  move: h; rewrite /is_fine -has_predC.
  case/hasP=> /= x hx1 hx2; apply/hasP; exists x => //=.
  move/part_size: hx1; rewrite leq_eqVlt eq_sym.
  by move: hx2; rewrite /is_trivial; move/negPf->.
-  have : hd \in s by rewrite e mem_head.
   rewrite /s mem_filter; case/andP=> _.
   by rewrite (perm_mem (gen_ordered_partition_perm_eq hm)).
Qed.


(* Assia : weird phrasing : why not (_ != _) ?*)
Lemma choose_part_not_nil_kmap (hm : hash_map) : 
  ~~ is_fine (gen_partition hm) -> (choose_part_kmap hm == [::]) = false.
Proof.
move/not_fine_chosen_part_in_P/part_size.
by rewrite -size_eq0 lt0n => /negPf.
Qed.

Lemma not_fine_size_choose_part (hm : hash_map) : 
  ~~ is_fine (gen_partition hm) -> 1 < size (choose_part_kmap hm).
Proof.
move=> h.
(* TODO this is almost verbatim the proof of 
   not_fine_chosen_part_in_P. could prove the conj in one go*)
rewrite /choose_part_kmap; set s := (X in head _ X).
case e: s => [ | hd tl] //=.
- suff: s != [::] by rewrite e.
  rewrite /s -has_filter. 
  rewrite (perm_has _ (gen_ordered_partition_perm_eq hm)).
  move: h; rewrite /is_fine -has_predC.
  case/hasP=> /= x hx1 hx2; apply/hasP; exists x => //=.
  move/part_size: hx1; rewrite leq_eqVlt eq_sym.
  by move: hx2; rewrite /is_trivial; move/negPf->.
-  have : hd \in s by rewrite e mem_head.
   by rewrite /s mem_filter; case/andP.
Qed.


Lemma fresh_not_in_hashes (hm : hash_map) : fresh hm \notin (hashes_hm hm).
  Proof.
  rewrite /fresh.
  set s := hashes_hm hm.
  set max := foldl maxn 0 s.
  move: (foldl_max s 0); rewrite -/max=> [[max0|]].
  + suffices all0 : all (pred1 0) s.
      apply/memPn=> /= n nin; rewrite max0.
      by move: (in_all nin all0)=> /eqP ->.
    move/max_foldlP : max0=> /andP[_ ].
    move: s {max}=> s all_gt0.
    apply /allP=> /= n; rewrite -leqn0.
    by move: n; apply /allP.
  + rewrite /max{max}.
    elim: s 0=> [//| hd tl IHtl] n /=.
    set n' := maxn n hd.
    rewrite in_cons=> /orP[eq_hd|in_tl].
    - rewrite /negb in_cons (eqP eq_hd) gtn_eqF //=.
      move/eqP : eq_hd=> /max_foldlP/andP[_ all_gt_hd].
      suffices : all (<%O^~ hd.+1) tl.
        elim: tl {IHtl all_gt_hd}=> [//|hd2 tl2 IHtl2].
        by rewrite /= in_cons=> /andP[/gtn_eqF -> /IHtl2] /= ->.
      move: all_gt_hd.
      elim: tl{IHtl}=> [//| hd2 tl2 IHtl2].
      rewrite /= -nat_coq_le_nat -nat_coq_nat ltnS.
      by move=> /andP[-> /IHtl2 ->].
    - move: IHtl=> /(_ _ in_tl).
      rewrite /negb in_cons; case: ifP=> [//|_ _]; rewrite orbF.
      set N := foldl _ _ _.
      have /eqP/max_foldlP := eq_refl N.
      rewrite /n' -nat_coq_le_nat geq_max.
      move=> /andP[/andP[_ ]].
      case_eq (N.+1 == hd)=> [|//].
      by move=> /eqP <-; rewrite ltnn.
  Qed.

Lemma mem_choose_part_kmap_mult1Pn (hm : hash_map):
    ~~ is_fine (gen_partition hm) ->
     forall (bn : B * nat),
       bn \in choose_part_kmap hm ->
         ~~ mult1 (hashes_hm hm) bn.2.
  Proof.
move=> fineN bn.
rewrite /choose_part_kmap.
set s := (X in head _ X).
case e : s => [ | hd tl] //= hbn.
have : hd \in s by rewrite e mem_head.
rewrite /s mem_filter; case/andP=> /= hhd1 hhd2.
rewrite /mult1. rewrite count_map /preim /=.
suff: (2 <= count [pred x | x.2 == bn.2] hm)%N. (* by lia *)
  by move/ltn_eqF; rewrite eq_sym; move/negPf->.
have hhd3 : hd \in gen_partition hm.
  by rewrite -(perm_mem (gen_ordered_partition_perm_eq _)).
have aux : all [pred x | x.2 == bn.2] hd.
  by apply: (part_all_eq_hash_mem _ _ hm).
have /(leq_count_subseq [pred x | x.2 == bn.2]): subseq hd hm.
  by apply: partition_memP.
by apply: leq_trans; move: aux; rewrite all_count=> /eqP->.
Qed.

Lemma distinguished_mark (bn: B * nat) (hm : hash_map):
    uniq (bnodes_hm hm) ->
    ~~ is_fine (gen_partition hm) ->
       bn \in choose_part_kmap hm ->
         distinguished hm < distinguished (mark_kmap_2 bn.1 hm).
  Proof.
  rewrite /mark_kmap_2=> ubs_hm finePn in_part.
  have fst_inj : {in hm &, injective fst}.
  by apply /in_map_injP => //; rewrite (hm_zip hm) zip_uniq_l //.
  have has_bn :  (find (eq_bnode bn.1) hm < size (hashes_hm hm))%N.
  rewrite {1}(hm_zip hm) find_index_eq_bnode; last by apply size_proj.
  rewrite index_map_in //; last by apply in_part_in_bnodes_kmap.
  + rewrite size_map.
    by move/in_part_in_bnodes_kmap : in_part; rewrite index_mem.
    suffices H : forall (hm' : hash_map),
    distinguished hm' = num_uniq_hash hm'.
    rewrite !H /num_uniq_hash.
    set hm' := mark_hash_kmap_2 _ _ _.
    set h1 := hashes_hm hm.
    set h2 := hashes_hm hm'.
    have -> : h2 = hashes_hm (set_nth (bn.1,(fresh hm)) hm (find (eq_bnode bn.1) hm) (bn.1,(fresh hm))). by [].
    suffices -> :
      hashes_hm (set_nth (bn.1,(fresh hm))  hm             (find (eq_bnode bn.1) hm) (bn.1,(fresh hm)))
      =          set_nth       (fresh hm)   (hashes_hm hm) (find (eq_bnode bn.1) hm)       (fresh hm).
      (**  *)
     rewrite count_set_nth_ltn //.
     set h2' := set_nth _ _ _ _.
     rewrite -/h1.
     set n1 := count (mult1 h2') h1.
     set n2 := mult1 h2' (fresh hm).
     set bn1 := ((nth _ _ _):nat in X in _ < X).
     set n3 := mult1 h2' _.
     suffices -> : n2 = true.
       suffices subp :subpred (mult1 h1) (mult1 h2').
     case_eq n3.
         rewrite addnK=> n3T.
         rewrite /n1.
         have bn1_in : bn1 \in h1.
           by rewrite /bn1; apply mem_nth; rewrite has_bn.
         apply: lt_count_subpred=> /=; first by apply subp.
         exists bn1; apply /and3P;split=> //.
         suffices -> : bn1 = bn.2.
           by apply mem_choose_part_kmap_mult1Pn=> //.
           rewrite /bn1.
           suffices : nth (bn.1 ,fresh hm) hm (find (eq_bnode bn.1) hm) = bn.
           rewrite {2}(hm_zip hm).
           rewrite nth_zip ?size_proj //.
           by case: bn {in_part hm' h2 has_bn h2' n1 n2 n3 subp n3T bn1 bn1_in} => bb nn [_ ->].
           rewrite {3}(hm_zip hm).
           rewrite find_index_eq_bnode ?size_proj //.
           suffices bn_in : bn \in hm.
           by rewrite index_map_in // nth_index.
           by apply in_part_in_bnodes_kmap.
           (** EO Proof *)

       move=> _.
       (* suffices -> : n3 = false. *)
         rewrite addn1 subn0.
         suffices leq : count (mult1 h1) h1 <= n1.
           by apply : (leq_ltn_trans leq (ltnSn _)).
         rewrite /n1 -/h1.
           by apply (sub_count subp).

           (** subpred *)
         move=>/= n; rewrite /mult1 /h1/h2'.
         set hs := hashes_hm hm.
         rewrite count_set_nth_ltn //.
         set n0 := pred1 n _.
         move=> /eqP eq; rewrite eq.
         set n0' := pred1 _ _.
         suffices -> : n0' = false.
           suffices -> : n0 = false.
             by rewrite eqxx.
           rewrite /n0.
             suffices nin : n \in hs.
               suffices /count_memPn : (fresh hm) \notin hs.
                 rewrite /=.
                 move: eq.
                 case_eq (fresh hm == n)=> [|//].
                 by rewrite eq_sym=> /eqP -> -> //.
               by apply fresh_not_in_hashes.
             by apply count_mem_1_in.
           rewrite /n0'.
           set b := nth _ _ _.
           suffices count_mem_b : count_mem b hs > 1.
             apply: negPf; rewrite /pred1/=; apply (@neq_count_mem _ _ _ hs).
             by apply /negPf; apply gtn_eqF; rewrite eq.
           set p := choose_part_kmap hm.
           have in_P: p \in gen_partition hm.
             by apply not_fine_chosen_part_in_P.
           suffices all_eqb_p : all (eq_hash bn.2) p.
             suffices size_p_gt1 : size p > 1.
               suffices count_bn_gt1 : count (eq_hash bn.2) hm > 1.
                 suffices eq_count : count (eq_hash bn.2) hm = count_mem bn.2 (hashes_hm hm).
                   suffices -> : b = bn.2.
                     by rewrite -eq_count; apply count_bn_gt1.
                   rewrite /b.
                   suffices : nth (bn.1 ,fresh hm) hm (find (eq_bnode bn.1) hm) = bn.
                     rewrite {2}(hm_zip hm).
                     rewrite nth_zip ?size_proj //.
                     by case: bn {in_part hm' h2 has_bn h2' n1 n2 n3 n0' b all_eqb_p count_bn_gt1 eq_count bn1} => bb nn [_ ->].
                   rewrite {3}(hm_zip hm).
                   rewrite find_index_eq_bnode ?size_proj //.
                   suffices bn_in : bn \in hm.
                     by rewrite index_map_in // nth_index.
                   by apply in_part_in_bnodes_kmap.
                 by rewrite count_mult.
               apply: (leq_trans size_p_gt1).
               suffices -> : size p = count (eq_hash bn.2) p.
                 apply leq_count_subseq.
                 apply partition_memP.
                 by apply not_fine_chosen_part_in_P.
                 rewrite /p (mem_partP _ _ _ in_part in_P) /=.
                 by rewrite size_filter count_filter.
              - exact: not_fine_size_choose_part.
        - rewrite /p.
          by apply (part_all_eq_hash_mem _ _ _ in_part in_P).
        - rewrite /n2/mult1.
          rewrite count_set_nth_ltn //= eqxx /=.
         (* EO subpred *)
      (**  *)
          rewrite /n3.
          rewrite /mult1.
          suffices fresh_nin : count_mem (fresh hm) (hashes_hm hm) = 0.
            have : (nth (fresh hm) (hashes_hm hm) (find (eq_bnode bn.1) hm)) \in hashes_hm hm by apply mem_nth.
            move=> /count_mem_inP nth_in.
            have /neq_count_mem/negPf : count_mem (fresh hm) h1 != count_mem (nth (fresh hm) h1 (find (eq_bnode bn.1) hm)) h1.
              rewrite fresh_nin.
              apply /negPf.
              suffices /ltn_eqF -> : 0 < count_mem (nth (fresh hm) h1 (find (eq_bnode bn.1) hm)) h1.
                by [].
              by apply: (leq_ltn_trans _ nth_in).
            by rewrite eq_sym=> -> ; rewrite subn0 fresh_nin add0n eqxx.
          by apply /count_memPn; apply fresh_not_in_hashes.
        - set n0 := fresh hm.
          set b0 := bn.1.
          set i := find (eq_bnode b0) hm.
          rewrite proj1_set_nth_prod //.
        - by move: has_bn; rewrite size_map.
        - by apply num_triv_distinguished.
      Qed.

  Lemma markP_kmap (bn : B * nat) (hm : hash_map) :
    ~~ is_fine (gen_partition hm) ->
      uniq (bnodes_hm hm) ->
        bn \in choose_part_kmap hm ->
          M_kmap (mark_kmap_2 bn.1 hm) < M_kmap hm.
  Proof.
  rewrite /M_kmap/mark_kmap_2.
  set x := mark_hash_kmap_2 _ _ _.
  move=> finePn ubs bn_in_choose.
  have bn1_in : bn.1 \in bnodes_hm hm.
    move/in_part_in_bnodes_kmap: bn_in_choose=> {x}.
    by case: bn=> b n; rewrite {1}(hm_zip hm)=> /in_zip/=/andP[->].
  have -> : size x = size hm.
    by rewrite mark_size.
  suffices : distinguished hm < distinguished x.
    move=> lt_dhm_dx.
    rewrite -nat_coq_nat ltn_sub2lE //.
    rewrite /distinguished.
    suffices le_part_size : count (is_trivial (B:=B)) (gen_partition x) <= size x.
      apply (leq_trans le_part_size).
      by rewrite mark_size // leqnn.
    suffices le_size_partition_x : (size (gen_partition x)) <= (size x).
      have leq_count_size : count (is_trivial (B:=B)) (gen_partition x) <= size (gen_partition x).
        by rewrite -nat_coq_le_nat; apply count_size.
      by apply (leq_trans leq_count_size le_size_partition_x).
    by apply size_gen_partition.
  by apply distinguished_mark.
  Qed.

  (* TODO not longer necesary *)
  (* Lemma mark_inv_kmap (g : seq (triple I B L)) (hm : hash_map) b : *)
  (*     (* claim: we need new hypothesis get_bts =i bnodes_hm hm *) *)
  (*     get_bts g =i bnodes_hm hm -> (* new hypothesis *) *)
  (*     b \in get_bts g ->  *)
  (*     uniq (bnodes_hm hm) -> *)
  (*     good_hash_map_for g hm -> *)
  (*       good_hash_map_for g (mark_kmap_2 b hm).  *)
  (* Proof. *)
  (* move=> mem_eq bin huniq ghf. *)
  (* move=> mu mu_inj_bs b' b'in. *)
  (* rewrite /mark_kmap_2 /mark_hash_kmap_2. *)
  (* set i := find _ _. *)
  (* set v := (b, fresh hm). *)
  (* rewrite {1}set_nthE -has_find has_eq_bnodes -mem_eq bin. *)
  (* have e : take i hm ++ v :: drop i.+1 hm = set_nth v hm i v. *)
  (*   by rewrite set_nthE -has_find has_eq_bnodes -mem_eq bin. *)
  (* rewrite e. *)
  (* (* have {ghf} ghf := (ghf mu mu_inj_bs).*) *)
  (* set almost_hm := set_nth _ _ _ _.   *)
  (* rewrite /equations.fun_of_hash_map /=. *)
  (* have b'in_almost : b' \in bnodes_hm almost_hm. *)
  (*   rewrite -[almost_hm]e. *)
  (*   move: b'in; rewrite mem_eq -{1}[hm](cat_take_drop i). *)
  (*   rewrite /bnodes_hm !map_cat !mem_cat; case/orP; first by move->. *)
  (*   rewrite -[drop i _](cat_take_drop 1) drop_drop add1n map_cat mem_cat /=. *)
  (*   case/orP=> /= hb'; last by rewrite mem_cons // orbT. *)
  (*   suff -> : b = b' by rewrite inE eqxx orbT. *)
  (*   move: hb'. *)
  (*   rewrite [i]find_eq_bnode. *)
  (*   have/bnodes_hm_exists[n hn] : b \in bnodes_hm hm by rewrite -mem_eq. *)
  (*   rewrite -(index_bnodes hn) //. *)
  (*   by rewrite drop_index //= take0 /= in_cons orbF; move/eqP. *)
  (* have mu_inj_set : {in bnodes_hm almost_hm &, injective mu}. *)
  (*   move=> x y.  *)
  (*   suff aux t : t \in bnodes_hm almost_hm -> t \in bnodes_hm hm.  *)
  (*     by move/aux => hx /aux hy; apply: mu_inj_bs; rewrite ?mem_eq. *)
  (*   rewrite -[almost_hm]e /bnodes_hm !map_cat. *)
  (*   rewrite !mem_cat map_cons; case/orP. *)
  (*   - by apply: mem_subseq; apply: map_subseq; exact: take_subseq. *)
  (*   rewrite in_cons; case/orP. *)
  (*   - by move/eqP->; rewrite -/(bnodes_hm hm) -mem_eq. *)
  (*   by apply: mem_subseq; apply: map_subseq; exact: drop_subseq. *)
  (* rewrite /almost_hm set_nthE -has_find has_eq_bnodes -mem_eq bin e. *)
  (* rewrite bnodes_hm_index_size; last by rewrite map1_bnodesC ?map_f. *)
  (* rewrite bnodes_hm_index_size //; congr nat_inj. *)
  (* rewrite map1_bnodesC map1_map (nth_map (b',0)) /= index_map_in //. *)
  (* by rewrite bnodes_hm_index_ltn. *)
  (* Qed. *)

  Lemma fresh_map1 (hm : hash_map) (mu : B -> B):
    fresh hm = fresh (map1 mu hm).
  Proof. by rewrite /fresh hashes_of_map1. Qed.

  Lemma mark_post_rel_kmap :
    forall (b : B) (hm : hash_map) (mu : B -> B),
      b \in bnodes_hm hm ->
      {in bnodes_hm hm &, injective mu} -> perm_eq (mark_kmap_2 (mu b) (map1 mu hm)) (map1 mu (mark_kmap_2 b hm)).
  Proof.
  move=> b hm mu bin mu_inj.
  rewrite /mark_kmap_2/mark_hash_kmap_2.
  set mu_i := find _ _.
  set i := find _ _.
  set mu_v := fresh (map1 mu hm).
  set v := fresh hm.
  suffices -> : (set_nth (mu b, mu_v) (map1 mu hm) mu_i (mu b, mu_v)) = (map1 mu (set_nth (b, v) hm i (b, v))) by [].
  rewrite map1_map !set_nthE size_map.
  have -> : mu_i = i.
    rewrite /mu_i/i (find_index_eq_bnode); last by rewrite !size_map.
    rewrite {2}(hm_zip hm) (find_index_eq_bnode); last by rewrite !size_map.
    by rewrite index_map_in.
  rewrite -has_find has_eq_bnodes bin.
  rewrite map1_map map_cat map_take /= map_drop.
  by rewrite /mu_v -fresh_map1.
  Qed.

  Lemma fresh_perm (hm p : hash_map):
    (hashes_hm hm) =i (hashes_hm p) -> fresh hm = fresh p.
  Proof.
  move=> mem_eq ; rewrite /fresh.
  by rewrite !foldl_idx (eq_big_idem _ _ maxnn mem_eq).
  Qed.

  Lemma mark_perm_hm_kmap (b : B) (hm p : hash_map) :
      (* claim: we need new hypothesis b \in bnodes_hm and uniq (bnodes_hm hm)*)
      uniq (bnodes_hm hm) ->
      b \in bnodes_hm hm ->
      perm_eq hm p -> 
      perm_eq (mark_kmap_2 b hm) (mark_kmap_2 b p).
  Proof.
  move=> uniq_bn binhm peq.
  rewrite /mark_kmap_2.
  rewrite /mark_hash_kmap_2.
  rewrite {3}(hm_zip hm) {3}(hm_zip p) !find_index_eq_bnode ?size_proj //.
  rewrite (fresh_perm _ _ (perm_mem (perm_map snd peq))).
  set v := (b, fresh hm). 
  set k := index _ _.
  set l := index _ _.
  have peq_bnodes : perm_eq (bnodes_hm hm) (bnodes_hm p).
    exact: perm_eq_bnodes_hm.
  have binp : b \in bnodes_hm p by rewrite -(perm_mem peq_bnodes).    
  rewrite !set_nthE !bnodes_hm_index_ltn //.
  suff step : perm_eq (take k hm ++ drop k.+1 hm) (take l p ++ drop l.+1 p).
    rewrite -[(b, fresh _) :: _]/([:: _] ++ _) perm_catCA.
    rewrite -[X in take l p ++ X]/([:: _] ++ _) perm_sym perm_catCA perm_sym.
    by rewrite (perm_catl _ step).
  have ep : p = take l p ++ [:: nth v p l] ++ drop l.+1 p.
    by rewrite -[LHS](cat_take_drop l) (drop_nth v) // bnodes_hm_index_ltn.
  have ehm : hm = take k hm ++ [:: nth v hm k] ++ drop k.+1 hm.
    by rewrite -[LHS](cat_take_drop k) (drop_nth v) // bnodes_hm_index_ltn.
  suff e : nth v p l = nth v hm k.
    move: peq; rewrite {1}ep {1}ehm e perm_catCA perm_sym perm_catCA perm_cat2l.
    by rewrite perm_sym.
  case/bnodes_hm_exists: (binhm) => n in_hm.
  rewrite -[k](index_bnodes in_hm) // nth_index //.
  have {in_hm} in_p : (b, n) \in p by rewrite -(perm_mem peq).
  by rewrite -[l](index_bnodes in_p) ?nth_index // -(perm_uniq peq_bnodes).
  Qed.


  Lemma set_nth_map_fst (hm : hash_map) (b : B) (n0 : nat) :
    b \in (bnodes_hm hm) ->
    let i := index b (bnodes_hm hm) in
    bnodes_hm (set_nth (b, n0) hm i (b, n0))
    = set_nth b (bnodes_hm hm) i b.
  Proof.
  move=> bin i.
  rewrite !set_nthE.
  have -> : size hm = size (bnodes_hm hm) by rewrite size_map.
  rewrite !index_mem bin.
  by rewrite /bnodes_hm; rewrite map_cat map_take /= map_drop.
  Qed.

  Lemma set_nth_eq (T : eqType) (s : seq T) (t : T):
    t \in s -> set_nth t s (index t s) t = s.
  Proof.
  rewrite set_nthE index_mem=> tin.
  rewrite tin.
  have : let i := find (pred1 t) s in split_find_nth_spec (pred1 t) s (take i s) (drop i.+1 s) (nth t s i).
    by move=> i'; apply split_find_nth; rewrite has_pred1.
  move=> [b' s1 s2 /eqP -> _].
  by rewrite -cats1 -catA cat1s.
  Qed.

  Lemma mark_eq_bnodes :
    forall hm : hash_map,
      forall b : B, b \in bnodes_hm hm -> bnodes_hm hm = bnodes_hm (mark_kmap_2 b hm).
  Proof.
  move=> hm b bin.
  rewrite /mark_kmap_2/mark_hash_kmap_2.
  rewrite {4}(hm_zip hm) !find_index_eq_bnode; last by rewrite size_proj.
  set i := index _ _.
  rewrite set_nth_map_fst // set_nth_eq //.
  Qed.

  Lemma mark_ubs_kmap :
    forall hm : hash_map,
      uniq (bnodes_hm hm) -> forall b : B, b \in bnodes_hm hm -> uniq (bnodes_hm (mark_kmap_2 b hm)).
  Proof.
  move=> hm ubs b bin.
  rewrite /mark_kmap_2/mark_hash_kmap_2; move: (fresh hm)=> n0.
  rewrite {2}(hm_zip hm) !find_index_eq_bnode; last by rewrite size_proj. 
  by rewrite set_nth_map_fst // set_nth_eq.
  Qed.

  Lemma color_refineP_kmap (g : seq (triple I B L)) (hm : hash_map) : M_kmap (color_refine_kmap g hm) <= M_kmap hm.
  Proof. by []. Qed.
(* 
  Lemma gen_partition_perm_eq (hm1 hm2 : hash_map) :
     perm_eq hm1 hm2 -> perm_eq (gen_partition hm1) (gen_partition hm2).
  Proof.
  move: hm2.
  pose P (x : hash_map) (g : partition) := forall hm2, perm_eq x hm2 ->
  perm_eq g (gen_partition hm2).
  apply: (gen_partition_elim P); rewrite /P; last first.
  - move=> bn l ih hm2 heq.
  
  rewrite [partitionate]lock /=.
  Search gen_partition.
  rewrite -/(P hm1 (gen_partition hm1)).
  rewrite [P _ _]lock.
  funelim (gen_partition hm1) => /= hm2 hperm; last first. (* WARNING generates hyp names...*)
  - by move: hperm; rewrite perm_sym; move/perm_nilP->.
    rewrite [gen_partition hm2]gen_partition_unfold_eq.
    
  move=> hperm12.
  elim/gen_partition_elim: hm1.
  case: hm1 hperm12 => [| p hm1].
  Search _ partitionate. *)

  (* TODO : Move above *)
  Lemma perm_eq_hashes  (hm1 hm2 : hash_map) :  perm_eq hm1 hm2 ->
    perm_eq (hashes_hm hm1) (hashes_hm hm2).
  Proof. by move=> hm12; rewrite /hashes_hm perm_map. Qed.

  Lemma perm_eq_part_of (hm1 hm2 : hash_map) n :  perm_eq hm1 hm2 ->
       perm_eq (part_of hm1 n) (part_of hm2 n).
  Proof. by move=> hm12; rewrite /part_of perm_filter. Qed.

  Lemma choose_part_kmap_order (hm1 hm2 : equations.hash_map B) :
  perm_eq hm1 hm2 -> 
  perm_eq (choose_part_kmap hm1) (choose_part_kmap hm2).
  Proof.
  move=> hm12; rewrite /choose_part_kmap /gen_ordered_partition.
  set l1 := sort _ _; set l2 := sort _ _.
  have -> : l1 = l2.
     apply/perm_sort_leP; apply: perm_undup; apply: perm_mem. 
     exact: perm_eq_hashes.
  move: l2 {l1} => l.
  elim: l => [| x l ihl] //=.
  set s1 := size _; set s2 := size _.
  have -> : s1 = s2.
    rewrite {}/s1 {}/s2.
    apply: perm_size; exact: perm_eq_part_of.
  case: ifP=> hx //=.
  exact: perm_eq_part_of.
  Qed.

  Lemma choose_part_kmap_post_relabeling (hm : hash_map) (mu : B -> B) : 
     choose_part_kmap (map1 mu hm) = map1 mu (choose_part_kmap hm).
  Proof.
  rewrite /map1 -!map_comp !zip_map.
  pose f (i : B * nat) := ((mu \o fst) i, i.2).
  rewrite -/f /choose_part_kmap /gen_ordered_partition.
  set u1 := undup _; set u2 := undup _.
  have -> : u1 = u2.
    rewrite {}/u1 {}/u2 /hashes_hm -map_comp.
    have /eq_map-> : (snd \o f) =1 snd by move=> [x1 x2] //.
    done.
  move: (sort leq u2) => l {u1 u2}.
  pose p := [pred x : part | 1 < size x].
  rewrite -/p.
  elim: l => [| n l ihl] //=.
  have e : part_of [seq f i | i <- hm] n =
            map f (part_of hm n).
    by rewrite /part_of filter_map.
  by rewrite !e size_map; case: ifP.
  Qed.

(*TODO : is duplicate *)
  Lemma in_part_in_hm_kmap (bn : B * nat) (hm : hash_map) : 
    bn \in choose_part_kmap hm -> bn \in hm.
  Proof. exact: in_part_in_bnodes_kmap. Qed.

(*TODO : is duplicate *)
  Lemma choose_from_not_fine_kmap (hm : hash_map) :
   ~~ is_fine (gen_partition hm) ->
     (choose_part_kmap hm == [::]) = false.
  Proof. exact: choose_part_not_nil_kmap. Qed.

  Definition template_kmap := @template disp I B L nat_inj cmp
                                init_hash_kmap choose_part_kmap color_kmap color_refine_kmap
                                mark_kmap_2 M_kmap markP_kmap color_refineP_kmap.

  Lemma uniq_kmap (g : rdf_graph I B L) : uniq (template_kmap g).
  Proof.
  apply (@uniq_template disp I B L nat_inj nat_inj_ cmp init_hash_kmap good_init_kmap
           init_hash_ubs_kmap choose_part_kmap in_part_in_hm_kmap color_kmap
           color_refine_kmap color_good_hm_kmap color_ubs_kmap color_refine_good_hm_kmap
           color_refine_ubs_kmap mark_kmap_2 good_mark_kmap mark_ubs_kmap M_kmap
           markP_kmap color_refineP_kmap).
  by case: g.
  Qed.

  Definition kmap_rdf (g : rdf_graph I B L) : rdf_graph I B L :=
    mkRdfGraph (uniq_kmap g).

  Theorem kmap_isocan : (@effective_isocanonical_mapping I B L kmap_rdf).
  Proof.
  exact: (@template_isocan disp I B L nat_inj nat_inj_ cmp cmp_anti cmp_total cmp_trans
            can_extremum init_hash_kmap good_init_kmap init_hash_inj_rel_kmap init_hash_perm_graph_kmap
            init_hash_ubs_kmap choose_part_kmap choose_part_kmap_order
            choose_part_kmap_post_relabeling in_part_in_hm_kmap choose_from_not_fine_kmap
            color_kmap color_refine_kmap color_good_hm_kmap color_post_relabeling_kmap
            color_perm_graph_kmap color_perm_hm_kmap color_ubs_kmap
            color_refine_good_hm_kmap color_refine_post_relabeling_kmap
            color_refine_perm_graph_kmap color_refine_perm_hm_kmap color_refine_ubs_kmap
            mark_kmap_2 good_mark_kmap mark_post_rel_kmap mark_perm_hm_kmap mark_ubs_kmap
            M_kmap markP_kmap color_refineP_kmap).
  Qed.

End KmappingInstance.

