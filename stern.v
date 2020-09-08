(** * Stern Brocot
  Copyright INRIA (2014) Marelle Team (Jose Grimm).
*)

(* $Id: stern.v,v 1.6 2018/07/17 15:49:43 grimm Exp $ *)


Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp  Require Import bigop ssralg div ssrnum ssrint rat prime path binomial.
From mathcomp  Require Import tuple finset.
Set Warnings "notation-overridden".

Require Import fibm.


Set Implicit Arguments.
Unset Strict Implicit.


Unset Printing Implicit Defensive.

Import BinPos.
Import GRing.Theory Num.Theory.

(*
Warning: Overwriting previous delimiting key num in scope N_scope
Warning: Hiding binding of key N to nat_scope
Warning: Hiding binding of key Z to int_scope
*)

Delimit Scope int_scope with Z.  
Delimit Scope nat_scope with N.
 

Module Stern.



(** ** Integers as lists of booleans *) 

Section Lists.

Variable T: eqType.
Implicit Types a b: T.

Lemma starts_with_aP l a:
  reflect (exists s, l = a::s) (l==a :: behead l).
Proof.
apply:(iffP idP).
  by move/eqP => ->; exists (behead l).
by move => [s ->].
Qed.

Definition ends_with_a l a := 
  l == rcons (belast (head a l) (behead l)) a.

Definition ends_with_a' l a := 
  l == rcons (rev (behead (rev l))) a.

Lemma rev_behead_etc b l : rev (behead (rev (b :: l))) = belast b l.
Proof.
rewrite rev_cons -{2}(revK l).
by case: (rev l) => // a s; rewrite /= rev_cons belast_rcons rev_rcons.
Qed.

Lemma ends_with_aE a l: (ends_with_a l a) =  (ends_with_a' l a).
Proof.
by rewrite /ends_with_a /ends_with_a'; case:l => // b l; rewrite rev_behead_etc.
Qed.

Lemma ends_with_a_rcons a l: ends_with_a (rcons l a) a.
Proof. by rewrite /ends_with_a /=; case: l => // b l; rewrite belast_rcons. Qed.

Lemma ends_with_a_cons a b l: ends_with_a l a -> ends_with_a (b::l) a.
Proof.
by move/eqP => -> /=; rewrite - rcons_cons; apply: ends_with_a_rcons.
Qed.


Lemma ends_with_aP l a :
  reflect (exists w, l = (rcons w a)) (ends_with_a l a).
Proof.
apply: (iffP idP).
  by move/eqP ->; set x:=(belast _ _); exists x.
by move=> [w ->]; rewrite  ends_with_aE /ends_with_a' rev_rcons /= revK.
Qed.


Definition ends_with_ab l a b :=
  l == rcons (rcons (rev (behead (behead (rev l)))) a) b.


Lemma ends_with_abP l a b:
  reflect (exists w, l = rcons (rcons w a) b) (ends_with_ab l a b).
Proof.
apply: (iffP idP).
  by move/eqP ->; set x:=(rev _); exists x.
by move=> [w ->]; rewrite /ends_with_ab !rev_rcons /= revK.
Qed.

Lemma ends_with_ab_cons x l a b:
  ends_with_ab l a b -> ends_with_ab (x::l) a b.
Proof.
move/ ends_with_abP => [w ->].
by rewrite/ends_with_ab rev_cons !rev_rcons revK. 
Qed.

End Lists.



(** Conversion [nat -> positive] *)

Definition pos_of_nat' n := pos_of_nat n n.

Lemma bin_of_nato n:  bin_of_nat ((n.+1).*2.+1) = Npos (xI (pos_of_nat' n)).
Proof. by rewrite /bin_of_nat doubleS -{1} addnn; elim: {1 3}n. Qed.

Lemma bin_of_nate n:  bin_of_nat (n.+1).*2 = Npos (xO (pos_of_nat' n)).
Proof. by rewrite /bin_of_nat doubleS -{1} addnn -addnS; elim: {1 3}n. Qed.

Lemma pos_of_natK n: nat_of_pos (pos_of_nat' n) = n.+1.
Proof. exact: (bin_of_natK n.+1). Qed.

Lemma nat_of_pos_ne0 p: nat_of_pos p != 0.
Proof. by move: (nat_of_binK (Npos p)) => /=; case: (nat_of_pos p). Qed.

Lemma nat_of_posK p: pos_of_nat' (nat_of_pos p).-1 = p.
Proof.
have ni: injective Npos  by move => a b; case. 
by apply: ni; move: (nat_of_binK (Npos p)) => /=; case: (nat_of_pos p).
Qed.

Lemma nat_of_pos_inj: injective nat_of_pos. 
Proof.  
by move => u v /(congr1 predn) /(congr1 pos_of_nat'); rewrite !nat_of_posK.
Qed.

(** Conversions between integers and lists of booleans *)

Fixpoint list_of_pos p :=
   match p with
   | xO n => false:: list_of_pos n
   | xI n => true:: list_of_pos n
   | xH => [:: true]
end.

Definition list_of_num p :=  if p is Npos p then list_of_pos p else nil.

Fixpoint pos_of_list l :=
  match l with
    | [ :: _ ] => xH
    |  a :: l => if a then xI (pos_of_list l) else xO (pos_of_list l)
    | nil => xH
end.

Definition num_of_list l :=
  if l is a :: b then Npos (pos_of_list l) else 0%num.

Lemma list_of_posK: cancel list_of_pos pos_of_list.
Proof. by elim => // p /= -> ;case: p. Qed. 

Lemma list_of_numK: cancel list_of_num num_of_list.
Proof. by case => // p /=; rewrite -{2} (list_of_posK p);case: p. Qed.

Lemma pos_of_listK x: list_of_pos (pos_of_list (rcons x true)) = rcons x true.
Proof.
by elim: x => // a l /=; case: rcons  => // u v; case: a => /= ->.
Qed.

Lemma num_of_listK x: list_of_num (num_of_list (rcons x true)) = rcons x true.
Proof.
by move:(pos_of_listK x); rewrite /num_of_list; case: rcons. 
Qed.

Lemma num_of_listK' x:
  ends_with_a x true -> list_of_num (num_of_list x) = x.
Proof. by move/ends_with_aP => [l ->]; apply: num_of_listK. Qed.

Lemma num_of_list_false x: 
   num_of_list (rcons x false) = num_of_list (rcons x true).
Proof.
case: x => // a l; rewrite !rcons_cons /num_of_list; congr Npos.
rewrite -!rcons_cons; elim: (a::l) => // {a l} a l /= ->.
move: (rev_cons true (rev l))  (rev_cons false (rev l)); rewrite revK.
by rewrite split_rev (split_rev false) => <- <-.
Qed.

Lemma num_of_list_sizeK x: size (list_of_num (num_of_list x)) = size x.
Proof.
rewrite -(revK x);case: {x} (rev x) => // b l. 
by case: b; rewrite rev_cons ?num_of_list_false num_of_listK // !size_rcons.
Qed.

Lemma nat_list_succ' n: ends_with_a (list_of_num (bin_of_nat n.+1)) true.
Proof.
rewrite /ends_with_a /=; apply/eqP.
by elim: (pos_of_nat n n) => // p /= {1} -> /=; case: p.
Qed.

Lemma nat_list_succ n (q:= (list_of_num (bin_of_nat n.+1))):
  rev q =  true :: behead  (rev q).
Proof. by rewrite /q (eqP (nat_list_succ' n)) rev_rcons. Qed.

Fixpoint nat_of_list l :=
  if l is a:: b then let r := (nat_of_list b).*2 in if a then r.+1 else r
  else 0.

Lemma nat_of_list_rF l : nat_of_list l = nat_of_list (rcons l false).
Proof. by elim: l => // a s /= ->. Qed.

Lemma nat_of_list_rT l: 
  nat_of_list (rcons l true) =  nat_of_bin (num_of_list (rcons l true)).
Proof. 
elim: l => // a l /= -> /=; rewrite /num_of_list headI - headI.
by case:a; case: l => // a l; rewrite /= natTrecE. 
Qed.

Lemma nat_of_list_rT' l: ends_with_a l true -> 
  nat_of_list l =  nat_of_bin (num_of_list l).
Proof. by move/ends_with_aP => [w ->]; apply:nat_of_list_rT. Qed.

  
Definition base2rev (n:nat) := 
  nat_of_list (rev (list_of_num (bin_of_nat n))).

Lemma base2rev0: base2rev 0 = 0. 
Proof. by []. Qed.

Lemma base2rev_even n: base2rev (n.*2) = base2rev n. 
Proof.
by case:n => // n; rewrite /base2rev bin_of_nate /= rev_cons - nat_of_list_rF.
Qed.

Lemma base2rev_odd n: odd n ->
  base2rev n = nat_of_bin (num_of_list (rev (list_of_num (bin_of_nat n)))). 
Proof.
move/oddE ->; case: {n} (n./2)  => // n.
by rewrite /base2rev bin_of_nato /= rev_cons -nat_of_list_rT.
Qed.

Lemma odd_base2rev n: odd (base2rev n.+1).
Proof.
rewrite /base2rev nat_list_succ.
by case: behead => // b l /=; rewrite odd_double.
Qed.

Lemma base2rev_oddI n: odd n -> base2rev (base2rev n) = n.
Proof.
move => on; have eq1 :=(oddE on).
rewrite eq1 (base2rev_odd (odd_base2rev _)) - eq1 (base2rev_odd on).
rewrite nat_of_binK eq1.
case: {n on eq1} (n./2) => // n.
rewrite -{2} (bin_of_natK (n.+1).*2.+1) bin_of_nato /= rev_cons num_of_listK.
by rewrite  - rev_cons revK (list_of_numK (Npos (pos_of_nat' n)~1)).
Qed.

Lemma base2rev_oddII p (n := (base2rev p)):  base2rev (base2rev n) = n.
Proof.
by rewrite /n {n}; case: p => // n; apply: base2rev_oddI; exact: odd_base2rev.
Qed.

(** Base two log *)

Definition log2 n := size (list_of_num (bin_of_nat n)).

Lemma log2_0: log2 0 = 0.
Proof. by []. Qed.

Lemma log2_1: log2 1 = 1.
Proof. by []. Qed.

Lemma log2_eq0 n: (log2 n == 0) = (n == 0).
Proof.
by case: n => // n; rewrite /log2 (eqP (nat_list_succ' n)) size_rcons.
Qed.

Lemma log2S_k n: (log2 n.+1) = (log2 n.+1).-1.+1.
Proof. by move:(log2_eq0 n.+1); case: (log2 n.+1). Qed.

Lemma log2_bnd n (k := log2 n.+1): 2^(k.-1) <= n.+1 < 2^k.
Proof.
move /ends_with_aP:(nat_list_succ' n) => [w /= eq].
rewrite /k /log2 /= eq -(bin_of_natK n.+1) -(list_of_numK (_ n.+1)) /= eq.
rewrite size_rcons succnK; move: (w); clear; elim => // a l.
rewrite rcons_cons;case: (rcons l true).
   by rewrite /= leqn0  !expnS => /andP [/eqP ->]. 
move => b l'; set q := nat_of_bin _; set q' := nat_of_bin _.
have -> : q' = if a then q.*2.+1 else q.*2. 
  by rewrite /q/q' /=; case: (a);rewrite /= natTrecE.
rewrite /= !expn2S;case: (a). 
  by rewrite leq_Sdouble ltn_Sdouble.
by rewrite leq_double ltn_double.
Qed.

Lemma log2_pr n m: 2 ^ m <= n < 2^m.+1 -> log2 n = m.+1.
Proof.
case: n; first by rewrite leqn0 expn_eq0 => /andP [/andP []].
move => n; move:(log2_bnd n) => /andP [ea eb] /andP[ec ed].
apply /eqP; move: (leq_ltn_trans ec eb)  (leq_ltn_trans ea ed).
by rewrite {1 3}(log2S_k n) eqn_leq ltn_exp2l // ltn_exp2l //; move => -> ->.
Qed.

Lemma log2_double n: log2 ((n.+1).*2) = (log2 n.+1).+1.
Proof. 
apply: log2_pr. 
rewrite {1} (log2S_k n) !expn2S ltn_double leq_double; exact:(log2_bnd n). 
Qed.

Lemma log2_Sdouble n: log2 (n.*2.+1) = (log2 n).+1.
Proof. 
case: n => //n;apply: log2_pr. 
rewrite {1}(log2S_k n) !expn2S ltn_Sdouble leq_Sdouble; exact:(log2_bnd n). 
Qed.

Lemma exp2_log_even n: ~~ odd (2 ^(log2 n.+1)).
Proof. by rewrite (log2S_k n) expn2S odd_double. Qed.

Lemma log2_pow n: log2 (2^ n) = n.+1.
Proof. by apply:log2_pr; rewrite leqnn ltn_exp2l /=. Qed.

Lemma log2_pred_pow n: log2 ((2^ n).-1) =  n.
Proof.
case: n => //n; apply: log2_pr. 
by rewrite -ltnS prednK ?expn_gt0 // leqnn andbT ltn_exp2l.
Qed. 

Lemma elogn2_unique a b a' b':
   (a.*2.+1) * 2 ^ b =  (a'.*2.+1) * 2 ^ b' -> a = a'.
Proof.
move/eqP; wlog: a b a' b' / b <= b'.
   move =>h; case/orP: (leq_total b b') => h'; first by apply: h.
   by rewrite eq_sym; move /(h _ _ _ _ h').
move => la; rewrite - (subnK la) expnD mulnA eqn_pmul2r ?expn_gt0 // => /eqP h.
move:(congr1 odd h); rewrite odd_mul /= !odd_double /= odd_exp orbF => ha.
by move /eqP: h; rewrite (eqP (esym ha))  muln1 eqSS eqn_double => /eqP.
Qed.

Lemma log2_mul_exp a n: a != 0 -> log2 (a* 2^n) = n + log2 a.
Proof.
move=> ap;elim: n => [|n H]; rewrite ?muln1 // expnS mulnCA mul2n addSn -H.
have h: 0 < a * 2 ^ n by rewrite muln_gt0 expn_gt0 lt0n (negbTE ap).
by rewrite -(prednK h) log2_double.
Qed.

Lemma leqn_log m n: m <= n -> log2 m <= log2 n.
Proof.
case:m => //; case:n=> // m n le1.
move: (log2_bnd n) (log2_bnd m) => /andP[e1 _]/andP[_ e4].
by move: (leq_ltn_trans (leq_trans e1 le1) e4); rewrite ltn_exp2l //-{1}log2S_k.
Qed.

Lemma log2_pr1 n (q := 2^ (log2 n).-1) :  n !=0 -> n = q + (n %% q).
Proof.
rewrite /q {q};case: n => // n _;apply/eqP;move:(log2_bnd n) => /=.
rewrite {2}(log2S_k n) expn2S -addnn; set q := 2^ _;case/andP => [ea].
rewrite - {1 2 3}(subnKC ea) ltn_add2l eqn_add2l => /modn_small <-.
by rewrite modnDl modn_mod. 
Qed.

Lemma base2r_odd n: base2rev (n.*2.+1) = 2^ (log2 n) + base2rev n.
Proof.
case: n => // n; rewrite /base2rev /log2 bin_of_nato /= rev_cons - size_rev.
by elim: (rev _) => // a l /= ->; rewrite doubleD -expn2S -addnS; case: a.
Qed. 

Lemma log_base2r n: odd n -> log2 (base2rev n) = log2 n.
Proof.
suff H: forall m, odd m -> log2 m <= log2 (base2rev m).
  move => on;move: (H _ on) (H _ (odd_base2rev n.-1)).
  have ->: n.-1.+1 = n by move: on; case n.
  by rewrite (base2rev_oddI on) =>sa sb; apply /eqP; rewrite eqn_leq sa sb.
move => m on; rewrite (oddE on) base2r_odd log2_Sdouble.
by case:m./2 => // m1; rewrite - log2_pow; apply:leqn_log; apply leq_addr.
Qed. 


Definition natnat_to_nat1 em := (2 ^ (em.1) * (em.2).*2.+1).-1.
Definition natnat_to_nat1_inv n := elogn2 0 n n.


Lemma natnat_to_nat1_bij: bijective natnat_to_nat1.
Proof.                         
have C1: cancel natnat_to_nat1_inv natnat_to_nat1.
  move => n.
  rewrite /natnat_to_nat1_inv /natnat_to_nat1.
  by case (elogn2P n) => e m /= <-.
exists natnat_to_nat1_inv => //.
apply: (inj_can_sym C1) => p q.
rewrite /natnat_to_nat1.
set c := _*_; set c' := _ * _.
have /prednK cp: 0 < c by rewrite /c muln_gt0 expn_gt0.
have /prednK cp': 0 < c' by rewrite /c muln_gt0 expn_gt0.
move/(f_equal (fun t => t.+1)); rewrite cp cp' => /eqP eq_cc.
rewrite (surjective_pairing p)  (surjective_pairing q).
move: eq_cc; rewrite /c/c'.
move: p.1 p.2 q.1 q.2 => a b a' b'.
wlog: a b a' b' / a <= a'.
   move =>h; case/orP: (leq_total a a') => h'; first by apply: h.
   by rewrite eq_sym; move /(h _ _ _ _ h').
move => la;rewrite - (subnKC la) expnD -mulnA eqn_pmul2l ?expn_gt0 // => /eqP h.
move:(congr1 odd h); rewrite odd_mul /= !odd_double /= andbT odd_exp orbF => ha.
move /eqP: h; rewrite (eqP (esym ha)) mul1n /= eqSS eqn_double addn0 => /eqP.
by move => ->.
Qed.

Definition natnat_to_nat2 p := p.1 + 'C((p.1+p.2).+1, 2).

Lemma natnat_to_nat2_inj: injective natnat_to_nat2.
Proof.
pose g a  := binomial a.+1 2.
pose f a b := a + g (a+b).  
move => p1 p2.
rewrite {2} (surjective_pairing p1) {2} (surjective_pairing p2).
set a1 := p1.1; set  a2 := p2.1; set b1 := p1.2; set b2 := p2.2.
rewrite /natnat_to_nat2 -/(f a1 b1) -/(f a2 b2) => eqa.
have Ha a: g a.+1 = g a + a.+1 by rewrite /g  binS bin1.
have Hb a b: g (a+b) <= f a b < g((a+b).+1).
  by rewrite /f leq_addl /= Ha addnS ltnS addnC addnA leq_addr.
have Hc a b: g a < g (b.+1) -> a <= b. 
  case: (leqP a b) => //; rewrite -ltnS (ltnNge (g a))/g.
  by move/(leq_bin2l 2) ->.
move: (Hb a1 b1) (Hb a2 b2); rewrite eqa => /andP[la lb] /andP[lc ld].
move: (leq_ltn_trans la ld) (leq_ltn_trans lc lb).
move => /Hc l1 /Hc l2.
have eqb: a1 + b1 == a2 + b2 by rewrite eqn_leq l1 l2.
move /eqP: eqa; rewrite /f (eqP eqb) eqn_add2r => /eqP eqc.
by move: eqb; rewrite eqc eqn_add2l => /eqP ->.
Qed.

Definition natnat_to_nat2_inv n :=
  let m := Nat.sqrt n.*2 in
  let s :=  if m * m.+1  <= n.*2 then  m else m.-1 in
  let a := n - 'C(s.+1, 2) in (a, s-a).

Lemma natnat_to_nat2_bij: bijective natnat_to_nat2.
Proof.
suff C1: cancel natnat_to_nat2_inv natnat_to_nat2.
  exists natnat_to_nat2_inv => //.
  by apply: (inj_can_sym C1); apply: natnat_to_nat2_inj.
move => n; rewrite /natnat_to_nat2_inv.
set m := Nat.sqrt _.
set s := if m * m.+1 <= n.*2 then m else m.-1.
suff /andP[ha hb]: 'C(s.+1, 2) <= n < 'C(s .+2, 2).
  have eq1: n - 'C(s.+1, 2) <= s.
    rewrite - (leq_add2r 'C(s.+1, 2)) (subnK ha).
    by move: hb; rewrite  binS bin1 addnS ltnS addnC.
  by rewrite /natnat_to_nat2 /= subnKC // subnK.
have bind k: 'C(k.+1,2).*2 = k * k.+1.
  elim:k => // k hr.
  by rewrite binS bin1 doubleD hr - mul2n - mulnDl addn2 mulnC.
have/andP[sa sb]: m^2 <= n.*2 < m.+1^2
    by move: (PeanoNat.Nat.sqrt_spec' n.*2)=> [/leP -> /leP ->].
rewrite /s. 
case: (leqP (m * m.+1)(n.*2)) => ha.
  rewrite - leq_double bind ha /= -leq_double bind doubleS mulSn mulnS !addSn.
  move: sb; rewrite - mulnn !mulnS mulSn addSn !ltnS => h.
  by apply:(leq_trans h); apply: leq_addl.
have mp: m = m.-1.+1 by move: ha; case:(m).
rewrite - mp -leq_double - (leq_double n.+1) bind doubleS ltn_neqAle ha.
have ->:n.*2.+1 != m * m.+1.
  by apply /negP; move /eqP /(f_equal odd); rewrite -bind /= !odd_double.
move: sa; rewrite mp bind -mulnn mulSnr => sa; rewrite(leq_trans _ sa) //.
apply: leq_addr.
Qed.



(* Merge two lists, padding with false the smallest *)

Fixpoint nn_to_n_merge1 l1:=
  if l1 is a::l then a:: false:: (nn_to_n_merge1 l) else nil.
Fixpoint nn_to_n_merge2 l2 :=
  if l2 is a::l then false:: a::(nn_to_n_merge2 l) else nil.

Fixpoint nn_to_n_merge l1 l2:=
  if l1 is a::l then
    if l2 is b::s then a::b:: nn_to_n_merge l s else nn_to_n_merge1 l1
  else nn_to_n_merge2 l2.

Fixpoint nn_to_n_split l: (seq bool * seq bool) :=
  if l is a::l1
  then if l1 is b::l2
       then let r := nn_to_n_split l2 in (a:: r.1, b:: r.2)
       else ([::a], [::false])
  else (nil,nil).


Definition natnat_to_nat3 p :=
  nat_of_list(nn_to_n_merge (list_of_num (bin_of_nat p.1))
                            (list_of_num (bin_of_nat p.2))).

Definition natnat_to_nat3_inv n :=
  let r := nn_to_n_split (list_of_num (bin_of_nat n))
  in (nat_of_list r.1, nat_of_list r.2).


Lemma nn_to_n_check_end l:
  exists w k, l = w ++ nseq k false /\ (w== nil) || ends_with_a w true.
Proof.
elim: l; first by exists nil,0. 
move => a l [w [k [-> /orP []]]].
  move/eqP ->; case:a; [ by exists [:: true], k |  by exists nil, k.+1 ].
by move => /(ends_with_a_cons a); exists (a::w),k. 
Qed.

Lemma nat_of_list_ext k l: nat_of_list (l ++ nseq k false) = nat_of_list l.
Proof.
elim:k l => [l | n H l /=]; first by rewrite cats0. 
by rewrite - cat_rcons H - nat_of_list_rF.
Qed.



Lemma nn_to_n_splitK l (r := nn_to_n_split l):
  nn_to_n_merge r.1 r.2 = l ++ nseq (odd (size l)) false.
Proof.
rewrite /r {r}; move: (eq_refl (half(size l))). 
move:{1} (half (size l)) => k; elim: k l.
  by case => // a [// | b l ] /=; case: (size l) => // n; case: (odd (n.+1)). 
move => n Hrec l.
by case:l => //a [  // | b l] /=; rewrite eqSS; move/Hrec => ->;rewrite negbK.
Qed.


Lemma nn_to_n_mergeK l1 l2:
  (nn_to_n_split (nn_to_n_merge l1 l2)) =
  (l1 ++ nseq (size l2 - size l1) false,  l2++ nseq (size l1 - size l2) false).
Proof.
have Hl l: (nn_to_n_split (nn_to_n_merge1 l)) = (l, nseq (size l) false).
  by elim:l => // a l /= ->.
elim: l1 l2; first by elim => // a l /= ->; rewrite subn0.
move => a l Hrec.
case; [ by rewrite /= Hl cats0 | by move => b l2; rewrite /= Hrec].
Qed.
 
Lemma nn_to_n_merge_ext l1 l2 k1 k2
      (delta := fun a b => (a-b)+ (b-a))
      (k3 := (delta (size (l1 ++ nseq k1 false)) (size (l2 ++ nseq k2 false)))
              +k1 + k2 - delta (size l1) (size l2)):
  nn_to_n_merge (l1 ++ nseq k1 false) (l2 ++ nseq k2 false)
  = (nn_to_n_merge l1 l2) ++ nseq k3 false.
Proof.
have Ha l: nn_to_n_merge l [::] = nn_to_n_merge1 l by case:l.
have Hb a: delta 0 a = a by rewrite /delta sub0n subn0. 
have Hc a: delta a 0 = a by rewrite /delta sub0n subn0. 
have Hd a b: delta a (a+b) = b.
  rewrite /delta addKn.
  by move: (leq_addr b a); rewrite - subn_eq0 => /eqP -> //.
have He a b: delta a.+1 b .+1 = delta a b by rewrite /delta !subSS.
rewrite /k3 {k3}.
elim: l1  k1 l2 k2.
  simpl; elim.
    move => /= l k;  rewrite /= !Hb size_cat addn0 - addnA addKn size_nseq.  
    elim:l; first by elim:k => // n; rewrite addnS addSn /=; move ->.  
    by move => b l /= ->.
  move => n Hrec; case.
    case.
      move: (Hrec nil 0); rewrite Hb !size_cat ! size_nseq.
      by rewrite !addn0 ! Hc !subn0  addnS addSn /= Ha => ->. 
    move => m; move: (Hrec nil m); rewrite Hb !size_nseq !subn0 => /= ->.
    by rewrite !He !addnS addSn.
  move => b l k2. move: (Hrec l k2).  rewrite !Hb  !size_cat ! size_nseq.
  by rewrite /= addSn He addnS addSn subSS => ->. 
move => a l Hrec k1; case.
   case.
     by move:(Hrec k1 nil 0); rewrite !Ha ! Hc ! addn0 /= => ->.
   move => n; move:(Hrec k1 nil n) => /= -> /=.
   by rewrite Ha  ! Hc He/= addnS subSS.
by move => b l2 k2; move:(Hrec k1 l2 k2) => /=  ->. 
Qed.


Lemma nn_to_n_split_ext l k
      (r1 := nn_to_n_split l)
      (r2 := nn_to_n_split (l ++ nseq k false))
      (k1 := if (odd k && ~~odd (size l)) then (k.+1)./2 else k./2):
      r2 == (r1.1 ++ nseq k1 false, r1.2 ++ nseq k1 false).
Proof.
rewrite /r1 /r2/k1.
move:(eqxx (size l)./2); set s := (size l)./2; rewrite {1}/s; move:s => s.
clear r1 r2 k1; elim: s l k.
  move => l k.
  have He n: nn_to_n_split (nseq n.*2 false) = (nseq n false, nseq n false).
    by elim:n => // n /= ->. 
  have Ho n: nn_to_n_split (nseq n.*2.+1 false)
      = (nseq n.+1 false, nseq n.+1 false).
    by elim:n => // n /= ->. 
  case:l => //.
    move => _ /=.
    move: (odd_double_half k); rewrite uphalf_half andbT => kv.
    by rewrite - [in (nseq _)] kv; case: (odd k); rewrite ?He ?Ho eqxx.
  move => a; case => // _; case:k => //. 
  move => n /=; move: (odd_double_half n); rewrite andbF uphalf_half => kv.
  by rewrite - [in (nseq _)] kv; case: (odd n); rewrite ?He ?Ho !eqxx.
move => n Hrec l k.
case: l => // a [ // | b l /= ]; rewrite negbK => ss.
by rewrite (eqP (Hrec l k ss)).
Qed.


Lemma natnat_to_nat3K: cancel natnat_to_nat3_inv natnat_to_nat3.
Proof.
have Hb l:  (l== nil) || ends_with_a l true -> 
   (list_of_num (bin_of_nat (nat_of_list l))) = l.
  case /orP; first by move/eqP ->.
  by move => H; rewrite (nat_of_list_rT' H) nat_of_binK num_of_listK'.
case => // n.
rewrite /natnat_to_nat3 /natnat_to_nat3_inv.
move:(nat_list_succ' n); set l := list_of_num _ => /= lp.
have ->: n.+1 = nat_of_bin (num_of_list l).
  by rewrite /l list_of_numK /= pos_of_natK.
move: (nn_to_n_check_end (nn_to_n_split l).1)  => [w1 [k1 [eql1 prop1]]].
move: (nn_to_n_check_end (nn_to_n_split l).2)  => [w2 [k2 [eql2 prop2]]].
rewrite eql1 eql2 !nat_of_list_ext (Hb _ prop1) (Hb _ prop2).
move: (nn_to_n_merge_ext w1 w2 k1 k2); rewrite -eql1 -eql2 => eql3.
move:(f_equal nat_of_list (nn_to_n_splitK l)); rewrite /= eql3 !nat_of_list_ext.
by move => ->; rewrite -(nat_of_list_rT' lp). 
Qed.
  
Lemma natnat_to_nat3_invK: cancel natnat_to_nat3 natnat_to_nat3_inv.
Proof.
have Hc a: nat_of_list (list_of_num (bin_of_nat a)) = a.
  case:a => // a. 
  by rewrite (nat_of_list_rT'  (nat_list_succ' a) ) list_of_numK bin_of_natK.
move => p.
rewrite /natnat_to_nat3 /natnat_to_nat3_inv.
rewrite [in RHS]  (surjective_pairing p).
move: p.1 p.2 => a b; clear p.
set qa :=  (list_of_num (bin_of_nat a)).
set qb :=  (list_of_num (bin_of_nat b)).
set r := (nn_to_n_merge qa qb). 
move: (nn_to_n_check_end r) => [w [k [rv etc]]].
have ->:  (list_of_num (bin_of_nat (nat_of_list r))) = w.
   rewrite rv nat_of_list_ext; case/orP:etc; first by move /eqP ->.  
   move => /ends_with_aP [v vv].
   by rewrite vv nat_of_list_rT nat_of_binK num_of_listK.
move: (nn_to_n_split_ext w k); simpl; set k1:= if _ then _ else _.
rewrite - rv (surjective_pairing (nn_to_n_split r)) => /eqP [eqa eqb].
rewrite - (nat_of_list_ext k1 (nn_to_n_split w).1) - eqa.
rewrite - (nat_of_list_ext k1 (nn_to_n_split w).2) - eqb.
by rewrite /r (nn_to_n_mergeK qa qb) /= ! nat_of_list_ext ! Hc.
Qed.


Lemma natnat_to_nat3_bij: bijective natnat_to_nat3.
Proof.
exists natnat_to_nat3_inv.
  apply: natnat_to_nat3_invK.
apply: natnat_to_nat3K.
Qed.



(** ** Properties of fields *)
Section Field.

Local Open Scope ring_scope.

Lemma ratN_M (n m: nat) : (n*m)%N%:Q = (n)%:Q * (m)%:Q. 
Proof. by  rewrite - rmorphM. Qed.

Lemma ratN_D (n m: nat) : (n+m)%N%:Q = (n)%:Q + (m)%:Q. 
Proof. by  rewrite - rmorphD. Qed.

Lemma intr_N (t: int): (-t)%:Q = -(t%:Q). 
Proof.  by rewrite - (mulrN1 t%:~R) -(mulrN1 t) intrM //. Qed.

Variable F : fieldType.
Implicit Types x y : F.

Lemma addf_div1 x y: y != 0 -> 1 + x / y = (x+y) /y.
Proof. 
move: (oner_neq0 F) => ha hb.
by rewrite -(divff ha) addf_div // mul1r mulr1 addrC.
Qed.

Lemma subf_div1 x y: y != 0 -> 1 - x / y = (y - x) /y.
Proof. by move => h; rewrite -mulNr addf_div1 // addrC. Qed.

Lemma subf_div2 x y: y != 0 -> x / y - 1 = (x - y) /y.
Proof. by move => h; rewrite -opprB subf_div1 // -mulNr opprB. Qed.

Lemma invf_div x y: (x / y)^-1 = y /x.
Proof. by  rewrite invfM mulrC invrK. Qed.

Lemma addf_inv x y: y != 0 -> x + y^-1 = (x*y +1)/y.
Proof. by move => h; rewrite mulrDl div1r mulfK. Qed.

Lemma doubleq (x: rat): x *2%:Q = x + x.
Proof. by rewrite - mulr2n  mulr_natr. Qed.

End Field.


(** ** Division in Z; copy of a part of intdiv  *)

Section Divz.

Local Open Scope ring_scope.


Definition divz (m d : int) :=
  let: (K, n) := match m with Posz n => (Posz, n) | Negz n => (Negz, n) end in
  sgz d * K (n %/ `|d|)%N.

Definition modz (m d : int) : int := m - divz m d * d.

Infix "%/" := divz : int_scope.
Infix "%%" := modz : int_scope.

Lemma divz_nat (n d : nat) : (n %/ d)%Z = n %/ d.
Proof. by case: d => // d; rewrite /divz /= mul1r. Qed.

Lemma divzN m d : (m %/ - d)%Z = - (m %/ d)%Z.
Proof. by case: m => n; rewrite /divz /= sgzN abszN mulNr. Qed.

Lemma divz_abs m d : (m %/ `|d|)%Z = (-1) ^+ (d < 0)%R * (m %/ d)%Z.
Proof.
by rewrite {3}[d]intEsign !mulr_sign; case: ifP => -> //; rewrite divzN opprK.
Qed.

Lemma div0z d : (0 %/ d)%Z = 0.
Proof.
by rewrite -(canLR (signrMK _) (divz_abs _ _)) (divz_nat 0) div0n mulr0.
Qed.

Lemma divNz_nat m d : (d > 0)%N -> (Negz m %/ d)%Z = - (m %/ d).+1%:Z.
Proof. by case: d => // d _; apply: mul1r. Qed.

Lemma divz_eq m d : m = (m %/ d)%Z * d + (m %% d)%Z.
Proof. by rewrite addrC subrK. Qed.

Lemma modzN m d : (m %% - d)%Z = (m %% d)%Z.
Proof. by rewrite /modz divzN mulrNN. Qed.

Lemma modz_abs m d : (m %% `|d|%N)%Z = (m %% d)%Z.
Proof. by rewrite {2}[d]intEsign mulr_sign; case: ifP; rewrite ?modzN. Qed.

Lemma modz_nat (m d : nat) : (m %% d)%Z = m %% d.
Proof.
by apply: (canLR (addrK _)); rewrite addrC divz_nat {1}(divn_eq m d).
Qed.

Lemma modNz_nat m d : (d > 0)%N -> (Negz m %% d)%Z = d%:Z - 1 - (m %% d)%:Z.
Proof.
rewrite /modz => /divNz_nat->; apply: (canLR (addrK _)).
rewrite -!addrA -!opprD -!PoszD -opprB mulnSr !addnA PoszD addrK.
by rewrite addnAC -addnA mulnC -divn_eq.
Qed.

Lemma modz_ge0 m d : d != 0 -> 0 <= (m %% d)%Z.
Proof.
rewrite -absz_gt0 -modz_abs => d_gt0.
case: m => n; rewrite ?modNz_nat ?modz_nat // -addrA -opprD subr_ge0.
by rewrite lez_nat ltn_mod.
Qed.

Lemma divz0 m : (m %/ 0)%Z = 0. Proof. by case: m. Qed.
Lemma mod0z d : (0 %% d)%Z = 0. Proof. by rewrite /modz div0z mul0r subrr. Qed.
Lemma modz0 m : (m %% 0)%Z = m. Proof. by rewrite /modz mulr0 subr0. Qed.


Lemma divz_small m d : 0 <= m < `|d|%:Z -> (m %/ d)%Z = 0.
Proof.
rewrite -(canLR (signrMK _) (divz_abs _ _)); case: m => // n /divn_small.
by rewrite divz_nat => ->; rewrite mulr0.
Qed.

Lemma divzMDl q m d : d != 0 -> ((q * d + m) %/ d)%Z = q + (m %/ d)%Z.
Proof.
rewrite neqr_lt -oppr_gt0 => nz_d.
wlog{nz_d} d_gt0: q d / d > 0; last case: d => // d in d_gt0 *.
  move=> IH; case/orP: nz_d => /IH// /(_  (- q)).
  by rewrite mulrNN !divzN -opprD => /oppr_inj.
wlog q_gt0: q m / q >= 0; last case: q q_gt0 => // q _.
  move=> IH; case: q => n; first exact: IH; rewrite NegzE mulNr.
  by apply: canRL (addKr _) _; rewrite -IH ?addNKr.
case: m => n; first by rewrite !divz_nat divnMDl.
have [le_qd_n | lt_qd_n] := leqP (q * d) n.
  rewrite divNz_nat // NegzE -(subnKC le_qd_n) divnMDl //.
  by rewrite -!addnS !PoszD !opprD !addNKr divNz_nat.
rewrite divNz_nat // NegzE -PoszM subzn // divz_nat.
apply: canRL (addrK _) _; congr _%:Z; rewrite addnC -divnMDl // mulSnr.
rewrite -{3}(subnKC (ltn_pmod n d_gt0)) addnA addnS -divn_eq addnAC.
by rewrite subnKC // divnMDl // divn_small ?addn0 // subnSK ?ltn_mod ?leq_subr.
Qed.

Lemma mulzK m d : d != 0 -> (m * d %/ d)%Z = m.
Proof. by move=> d_nz; rewrite -[m * d]addr0 divzMDl // div0z addr0. Qed.

Lemma mulKz m d : d != 0 -> (d * m %/ d)%Z = m.
Proof. by move=> d_nz; rewrite mulrC mulzK. Qed.

Lemma expzB p m n : p != 0 -> (m >= n)%N ->
  p ^+ (m - n) = (p ^+ m %/ p ^+ n)%Z.
Proof. by move=> p_nz /subnK{2}<-; rewrite exprD mulzK // expf_neq0. Qed.

Lemma modz1 m : (m %% 1)%Z = 0.
Proof. by case: m => n; rewrite (modNz_nat, modz_nat) ?modn1. Qed.

Lemma divn1 m : (m %/ 1)%Z = m. Proof. by rewrite -{1}[m]mulr1 mulzK. Qed.

Lemma divzz d : (d %/ d)%Z = (d != 0).
Proof. by have [-> // | d_nz] := altP eqP; rewrite -{1}[d]mul1r mulzK. Qed.

Lemma ltz_pmod m d : d > 0 -> (m %% d)%Z < d.
Proof.
case: m d => n [] // d d_gt0; first by rewrite modz_nat ltz_nat ltn_pmod.
by rewrite modNz_nat // -lez_addr1 addrAC subrK ger_addl oppr_le0.
Qed.


Lemma ltz_mod m d : d != 0 -> (m %% d)%Z < `|d|.
Proof. by rewrite -absz_gt0 -modz_abs => d_gt0; apply: ltz_pmod. Qed.

Lemma divzMpl p m d : p > 0 -> (p * m %/ (p * d) = m %/ d)%Z.
Proof.
case: p => // p p_gt0; wlog d_gt0: d / d > 0; last case: d => // d in d_gt0 *.
  by move=> IH; case/intP: d => [|d|d]; rewrite ?mulr0 ?divz0 ?mulrN ?divzN ?IH.
rewrite {1}(divz_eq m d) mulrDr mulrCA divzMDl ?mulf_neq0 ?gtr_eqF // addrC.
rewrite divz_small ?add0r // PoszM pmulr_rge0 ?modz_ge0 ?gtr_eqF //=.
by rewrite ltr_pmul2l ?ltz_pmod.
Qed.


Arguments divzMpl [p m d].

Lemma divzMpr p m d : p > 0 -> (m * p %/ (d * p) = m %/ d)%Z.
Proof. by move=> p_gt0; rewrite -!(mulrC p) divzMpl. Qed.
Arguments divzMpr [p m d].

Lemma lez_floor m d : d != 0 -> (m %/ d)%Z * d <= m.
Proof. by rewrite -subr_ge0; apply: modz_ge0. Qed.

Lemma lez_div m d : (`|(m %/ d)%Z| <= `|m|)%N.
Proof.
wlog d_gt0: d / d > 0; last case: d d_gt0 => // d d_gt0.
  by move=> IH; case/intP: d => [|n|n]; rewrite ?divz0 ?divzN ?abszN // IH.
case: m => n; first by rewrite divz_nat leq_div.
by rewrite divNz_nat // NegzE !abszN ltnS leq_div.
Qed.
 
Lemma ltz_ceil m d : d > 0 -> m < ((m %/ d)%Z + 1) * d.
Proof.
by case: d => // d d_gt0; rewrite mulrDl mul1r -ltr_subl_addl ltz_mod ?gtr_eqF.
Qed.

Lemma ltz_divLR m n d : d > 0 -> ((m %/ d)%Z < n) = (m < n * d).
Proof.
move=> d_gt0; apply/idP/idP.
  by rewrite -lez_addr1 -(ler_pmul2r d_gt0); apply: ltr_le_trans (ltz_ceil _ _).
rewrite -(ltr_pmul2r d_gt0 _ n) //; apply: ler_lt_trans (lez_floor _ _).
by rewrite gtr_eqF.
Qed.

Lemma lez_divRL m n d : d > 0 -> (m <= (n %/ d)%Z) = (m * d <= n).
Proof. by move=> d_gt0; rewrite !lerNgt ltz_divLR. Qed.


Lemma divz_ge0 m d : d > 0 -> ((m %/ d)%Z >= 0) = (m >= 0).
Proof. by case: d m => // d [] n d_gt0; rewrite (divz_nat, divNz_nat). Qed.

Lemma divzMA_ge0 m n p : n >= 0 -> (m %/ (n * p) = (m %/ n)%Z %/ p)%Z. 
Proof.
case: n => // [[|n]] _; first by rewrite mul0r !divz0 div0z.
wlog p_gt0: p / p > 0; last case: p => // p in p_gt0 *.
  by case/intP: p => [|p|p] IH; rewrite ?mulr0 ?divz0 ?mulrN ?divzN // IH.
rewrite {2}(divz_eq m (n.+1%:Z * p)) mulrA mulrAC !divzMDl // ?gtr_eqF //.
rewrite [rhs in _ + rhs]divz_small ?addr0 // ltz_divLR // divz_ge0 //.
by rewrite mulrC ltz_pmod ?modz_ge0 ?gtr_eqF ?pmulr_lgt0.
Qed.

Lemma modz_small m d : 0 <= m < d -> (m %% d)%Z = m.
Proof. by case: m d => //= m [] // d; rewrite modz_nat => /modn_small->. Qed.

End Divz.

(* again outside the section *)
Infix "%/" := divz : int_scope.
Infix "%%" := modz : int_scope.

(** ** Floor on Q *)


Section Floorq.

Local Open Scope ring_scope.


Definition floorq x := ((numq x) %/ (denq x))%Z.

Lemma succq (z: int): z%:Q +1 = (z+1) %:Q.
Proof. by rewrite rmorphD. Qed.

Lemma floorp1 x (y:= (floorq x)%:Q): y <= x < y+1.
Proof.
have ha: 0 < (denq x)%:Q by rewrite  ltr0z (denq_gt0 x).
rewrite -(divq_num_den x) ler_pdivl_mulr // succq  ltr_pdivr_mulr //.
rewrite - !rmorphM /= ler_int ltr_int lez_floor // ltz_ceil //.
Qed.


Lemma floorp2 x (y: int): y%:Q <= x < y%:Q +1 ->  y = floorq x.
Proof.
move: (floorp1 x) => /andP [sa sb] /andP [sc sd].
apply/eqP;  rewrite eqr_le - !ltz_addr1 -! (ltr_int rat_numDomainType).
by rewrite - !succq (ler_lt_trans sc sb) (ler_lt_trans sa sd).
Qed.

Lemma floor_ge0 x: 0 <= x -> 0 <= floorq x.
Proof.
move /andP:(floorp1 x) => [la lb] lc. 
by move: (ler_lt_trans lc lb); rewrite  succq ltr0z ltz_addr1.
Qed.

Lemma floor_small x: 0 <= x < 1 -> floorq x = 0.
Proof. by symmetry; apply:floorp2;rewrite add0r. Qed.

Lemma floor_div (a b:int): 0 < b -> floorq (a%:Q / b%:Q) = (a %/b)%Z.
Proof.
rewrite /floorq; case: divqP => // k x _;rewrite (pmulr_lgt0 _ (denq_gt0 x)).
by move => h;rewrite divzMpl.
Qed.

Lemma floor_sum (a:rat) (b: int):  floorq (a + b%:Q) = floorq a + b.
Proof.
symmetry; apply:floorp2; case/andP:(floorp1 a) => [l1 l2].
by rewrite intrD ler_add2r l1 addrAC ltr_add2r l2.
Qed.


Lemma floor_succ a : floorq (a + 1) = (floorq a) + 1.
Proof. by rewrite -(floor_sum a 1). Qed.

(** the Stern succ function *)


Definition Stern_succ_fct x := (1 + (floorq x)%:Q *2%:Q - x)^-1.

Notation Sn := Stern_succ_fct. 


Definition Stern_prev_fct x  (y := (- x)^-1) := 
  y - 1 - (floorq y)%:Q * 2%:Q. 

(* ORIG
Lemma Stern_succ_fctK: cancel Sn  Stern_prev_fct.
Proof.
move => x;rewrite /Stern_prev_fct /Sn invrN invrK opprB - intrM.  
rewrite -{2}(intrD _ 1%:Z) -intr_N floor_sum - intrM - intr_N - mulNr opprB.
rewrite {2} mulz2 addrA addrK  -(addrA x) -opprD (addrC _ 1) - !(intrD _ 1%:Z).
by rewrite mulz2 mulz2 addrACA addrA addrNK. 
Qed.
*)


Lemma Stern_succ_fctK: cancel Sn  Stern_prev_fct.
Proof.
move => x;rewrite /Stern_prev_fct /Sn invrN invrK opprB - intrM.  
rewrite -{2}(intrD _ 1%:Z) -intr_N floor_sum - intrM - intr_N.
rewrite -[in  X in _ + X] mulNr  (opprB (floorq x)).
rewrite {2} mulz2 (addrA 1) addrK  -(addrA x) -opprD (addrC _ 1) - !(intrD _ 1%:Z).
by rewrite mulz2 mulz2 addrACA addrA addrNK. 
Qed.

(* ORIG 

Lemma Stern_prev_fctK: cancel Stern_prev_fct Sn.
Proof.
move => x; rewrite /Stern_prev_fct /Sn; set y := floorq (- x)^-1. 
rewrite - intrM - intrM - (addrA _ (-1)) - opprD -!(intrD _ 1%:Z) -{1} intr_N. 
rewrite floor_sum  opprD -/y addrCA - (opprB _ y) !mulz2 addrK !addrA opprB.
by rewrite addrN add0r - !opprD intr_N (addrC y) addKr invrN opprK invrK. 
Qed.
*)

Lemma Stern_prev_fctK: cancel Stern_prev_fct Sn.
Proof.
move => x; rewrite /Stern_prev_fct /Sn; set y := floorq (- x)^-1.
rewrite - intrM - intrM -[((- x)^-1 - 1 - (y * 2)%:~R)] addrA.
rewrite - (opprD 1) -!(intrD _ 1%:Z) -{1} intr_N. 
rewrite floor_sum  opprD (addrCA (floorq _)) - (opprB _ y) !mulz2 addrK.
have -> : (1 + (- (1) - y + (- (1) - y))) = (- (1 + y + y)).
  by rewrite !addrA addrN add0r - !opprD (addrC y).
by rewrite (addrA 1 y)  opprB intr_N addKr invrN opprK invrK. 
Qed.

Lemma Sn_0: Sn 0 = 1.  Proof. by []. Qed.
Lemma Sn_1: Sn 1 = 1/(2%:Q).  Proof. by []. Qed.

Lemma Sn_gt0 x: 0 <= x -> 0 < Sn x.
Proof.
rewrite /Sn doubleq addrA  (addrC (1 + _)) -addrA => h.
rewrite invr_gt0 -(addr0 0); apply:ler_lt_add;first by rewrite ler0z floor_ge0.
by rewrite subr_gt0 addrC; case /andP:(floorp1 x) => [_].
Qed.

Lemma Sn_small x: 0 <= x < 1 -> Sn x = (1-x) ^-1.
Proof. by rewrite /Sn; move/floor_small => ->; rewrite mul0r addr0. Qed.

(* ORIG

Lemma Sn_neg x  (T:= fun x => (- x)^-1):
  0 < x  -> Sn (T (Sn x)) = T x.
Proof.
move => xp; rewrite /T; congr (_ ^-1).
rewrite invrN opprK /Sn invrK opprB.
set W := (floorq x)%:~R; set t := (1 + W * 2%:~R); set a := (1 + (W + W)).
have ->: -t =  (- (1 + (floorq x) * 2%Z))%:Q.
  rewrite /t /W ! opprD intrD - intrM - mulrNz //=.
rewrite floor_sum intrD intr_N intrD intrM /t !doubleq -/W  (addrACA W). 
by rewrite -/a addrA addrA  addrCA subrr addr0 (addrC _ a) subrr add0r.
Qed.
*)

Lemma Sn_neg x  (T:= fun x => (- x)^-1):
  0 < x  -> Sn (T (Sn x)) = T x.
Proof.
move => xp; rewrite /T; congr (_ ^-1).
rewrite invrN (opprK (Sn x)^-1)  /Sn invrK opprB.
set W := (floorq x)%:~R; set t := (1 + W * 2%:~R); set a := (1 + (W + W)).
have ->: -t =  (- (1 + (floorq x) * 2%Z))%:Q.
  rewrite /t /W opprD opprD  intrD - intrM - mulrNz //=.
rewrite floor_sum intrD intr_N intrD intrM /t !doubleq -/W  (addrACA W). 
by rewrite -/a addrA addrA  addrCA subrr addr0 (addrC _ a) subrr add0r.
Qed.


Lemma Sn_lt1 (a b: int)  (A := a%:Q) (B := b%:Q):
  0 <= a -> 0 < b  -> Sn (A / (A + B)) = (A + B) / B.
Proof.
move => la lb; move: (ler_lt_add la lb); rewrite addr0 => lab.
have labq:  0 < (a + b)%:Q by rewrite ltr0z.
have dnz: (a + b)%:Q != 0 by move: labq; rewrite lt0r => /andP [].
have ha: 0 <= a%:Q / (a + b)%:Q < 1.
  rewrite divr_ge0 ?ler0z // ? (ltrW  lab)//= ltr_pdivr_mulr //.
  by rewrite mul1r  ltr_int - {1} (addr0  a) ltr_add2l.
rewrite Sn_small - intrD // -(invf_div b%:~R) subf_div1 //.
by rewrite - rmorphB /= {1} (addrC a) - addrA subrr addr0.
Qed.


Lemma Sn_gt1 (a b: int) (c := (a + b) - (a %% b)%Z *2) 
  (A := a%:Q) (B := b%:Q)  (C := c%:Q):
  0 <= a -> 0 < b ->  Sn ((A + B) / B) = B / (B + C).
Proof.
move => la lb; rewrite /Sn.
have lt1 := (ltz_pmod a lb).
have Bne: B != 0 by move: lb; rewrite lt0r intr_eq0  => /andP [].
rewrite - [in RHS] invf_div (addrC B) - addf_div1 // -addf_div1 //.
rewrite - addrA; congr ((1+  _) ^-1); rewrite opprD addrA -(addrK (A/B) (C/B)).
congr (_ - (A/B)); rewrite - mulrDl - intrD (addrC 1) floor_succ floor_div //.
rewrite doubleq - intrD addrACA  - (intrD _ _ (-1)%Z) addrA addrK.  
rewrite /c /modz mulrBl opprB mulrAC (addrC a) addrACA -{3} (mul1r b) -mulrDl.
by rewrite - mulz2 - addrA addrAC - mulz2 subrr addr0 intrM  addrC -/B mulrK. 
Qed.


End Floorq.

(** ** CF *)

Section ContinuedFractions.

Local Open Scope ring_scope.

Implicit Type L : seq rat.

Fixpoint SCF' L:= if L is (a::l) then 1 / (a + SCF' l) else 0.
Definition SCF L := if L is a::l then a + SCF' l else 0.

Lemma SCF_pos1 L : all (fun z => 0 < z) L -> L != nil -> 0 <  SCF' L.
Proof.
elim: L => // a L H /= /andP [ha hb] _; apply: divr_gt0 => //.
case lz: (L== nil); first by rewrite (eqP lz) addr0.
by apply: addr_gt0 => //; apply: H => //; rewrite lz.
Qed.

Lemma SCF_pos2 a L : all (fun z => 0 < z) L ->  a <= SCF (a::L).
Proof.
rewrite /SCF - {1}(addr0 a) ler_add2l.
case lz: (L== nil) => h; first by rewrite (eqP lz).
rewrite ltrW ?  SCF_pos1 ? lz //=.
Qed.

Lemma SCF_rec a l : SCF (a :: l) = a + 1 / SCF l.
Proof. by case: l. Qed.

Lemma SCF1 a  : SCF [:: a ] = a.
Proof. by rewrite /= addr0. Qed.

Lemma SCF2 a b : SCF [:: a ; b ] =  a + 1 / b.
Proof.  by rewrite SCF_rec SCF1. Qed.

Lemma SCF_cat L1 L2 : L1 != nil -> L2 != nil ->
   SCF (L1 ++ L2) = SCF(rcons L1 (SCF L2)).
Proof.
case: L1 => // a L1 _ h /=; congr(a + _).
elim: {a}L1 => //; first by rewrite /=addr0; move:h; case: L2 => //.
by move => a l /= ->.
Qed.

Lemma SCF_recl L a b: SCF (rcons (rcons L a) b) =  SCF (rcons L (a+1/b)).
Proof.
case: L; first by rewrite /SCF /=  !addr0.
by move => u v;rewrite - cats1 cat_rcons SCF_cat // SCF2.
Qed.


Lemma SCF_simpl1 l: SCF (0::l) = SCF' l.
Proof. by rewrite /= add0r. Qed.

Lemma SCF2_bis (a b: rat) : b != 0 -> 1/ (a + 1 / b) = b / (a * b + 1). 
Proof. by move => bz; rewrite !div1r addf_inv // invf_div. Qed.

Lemma SCF_zero_at_end L a: SCF (rcons (rcons L a) 0) =  SCF (rcons L a).
Proof. by rewrite SCF_recl invr0 mulr0 addr0. Qed.

Lemma SCF_simpl0 a b l l': SCF(l++a::0::b::l') = SCF(l++a+b::l').
Proof.
by elim:l=> [| c [ /=->  | d l /= ->]] //; rewrite /= add0r !div1r invrK addrA.
Qed.

Lemma SCF'_opp l: SCF' [seq -x | x <- l] = - SCF' l.
Proof. 
case: l => // a l; elim: l a => [a | b l H a].
  by rewrite /= !addr0 !div1r invrN.
by move: (H b) => /= ->; rewrite - opprD !div1r invrN.
Qed.

Lemma SCF_opp l: SCF [seq -x | x <- l] = - SCF l.
Proof. by case: l => // a l /=; rewrite opprD SCF'_opp. Qed.

(* ORIG

Lemma SCF_neg1 a b l l' (x := SCF' l') :  b - 1 - x != 0 ->  b - x != 0 ->
  SCF(l++a::-b::l') = SCF(l++a-1::1::b-1:: [seq -x | x <- l']).
Proof.
move => ha hb.
suff h: SCF [:: a, - b & l'] = SCF(a-1::1::b-1:: [seq -x | x <- l']).
  case lz: (l== nil);first by rewrite (eqP lz) h.
  by rewrite SCF_cat ?lz // SCF_cat ?lz // h.
rewrite/= SCF'_opp SCF2_bis// !mul1r addrAC -addrA (addrC _ x) ; congr (_ + _).
by rewrite addrAC addrK subf_div2 // (addrC (b-x)) addrK mulN1r - invrN opprB.
Qed.
*)


Lemma SCF_neg1 a b l l' (x := SCF' l') :  b - 1 - x != 0 ->  b - x != 0 ->
  SCF(l++a::-b::l') = SCF(l++a-1::1::b-1:: [seq -x | x <- l']).
Proof.
move => ha hb.
suff h: SCF [:: a, - b & l'] = SCF(a-1::1::b-1:: [seq -x | x <- l']).
  case lz: (l== nil);first by rewrite (eqP lz) h.
  by rewrite SCF_cat ?lz // SCF_cat ?lz // h.
rewrite/= SCF'_opp SCF2_bis// !mul1r addrAC -addrA (addrC _ x) ; congr (_ + _).
rewrite (addrAC b) (addrK  (- 1) (b - x)).
by rewrite  subf_div2 // (addrC (b-x)) addrK mulN1r - invrN opprB.
Qed.

Lemma SCF_neg2 a b l :  b != 1 ->  b != 0 ->
  SCF (rcons (rcons l a) (-b)) = SCF(rcons (rcons (rcons l (a-1)) 1) (b-1)).
Proof.
move => ha hb.
have ha': b - 1 - 0 != 0 by rewrite subr0 subr_eq0.
have hb': b - 0 != 0 by rewrite subr0 .
by move:(@SCF_neg1 a b l nil ha' hb'); rewrite /= - !cats1 - !catA.
Qed.

Lemma SCF_neg3 a l : SCF (rcons (rcons l a) (-1)) = SCF (rcons l (a-1)).
Proof. by rewrite SCF_recl mul1r. Qed.

Definition rat_in_Z (x: rat) := x == (floorq x)%:Q.
Definition int_in_N (x: int) := x == (absz x)%:Z.
Definition int_in_P (x: int) := x == (absz x).-1.+1%:Z.
Definition rat_in_N (x: rat) := rat_in_Z x && int_in_N (floorq x).
Definition rat_in_P (x: rat) := rat_in_Z x && int_in_P (floorq x).

Lemma rat_in_Z_int (x: int): rat_in_Z (x%:Q).
Proof. by rewrite /rat_in_Z /floorq numq_int denq_int divn1. Qed.

Lemma int_in_N_nat (x: nat): int_in_N (x%:Z).
Proof. by rewrite /int_in_N. Qed.

Lemma rat_in_N_nat (x: nat) : rat_in_N (x%:Z%:Q).
Proof. 
by rewrite /rat_in_N rat_in_Z_int /= /int_in_N /floorq numq_int denq_int divn1.
Qed.

Lemma rat_in_P_nat (x: nat) : rat_in_P (x.+1%:Z%:Q).
Proof. 
by rewrite /rat_in_P rat_in_Z_int /= /int_in_P /floorq numq_int denq_int divn1.
Qed.

Lemma rat_in_ZP x: reflect (exists n, x = n%:Q) (rat_in_Z x).
Proof.
apply:(iffP idP) => [h | [n ->]]; first by exists (floorq x); apply/eqP.
apply:rat_in_Z_int.
Qed.

Lemma int_in_NP x: reflect (exists n, x = n%:Z) (int_in_N x).
Proof.
apply:(iffP idP) => [h | [n ->]]; first by exists (absz x); apply/eqP.
apply:int_in_N_nat.
Qed.

Lemma rat_in_NP x: reflect (exists n, x = n%:Z%:Q) (rat_in_N x).
Proof.
apply:(iffP idP) => [h | [n ->]]; last by apply:rat_in_N_nat.
by move/andP:h => [/eqP {2} -> /int_in_NP [n ->]]; exists n.
Qed.

Lemma rat_in_PP x: reflect (exists n, x = n.+1%:Z%:Q) (rat_in_P x).
Proof.
apply:(iffP idP) => [h | [n ->]]; last by apply:rat_in_P_nat.
by move/andP:h => [/eqP {2} -> /eqP ha]; exists `|floorq x|.-1; rewrite - ha.
Qed.

Lemma rat_in_P_ge1 x: rat_in_P x -> 1 <= x.
Proof. by move/rat_in_PP => [n ->]; rewrite ler1n. Qed.

Definition good_for_cf a l:=  [&& rat_in_Z a, all rat_in_P l & last 0 l !=1].

Lemma all_rat_in_P_pos l: all rat_in_P l -> all (> 0) l. 
Proof.  
move => aa.
apply/allP => i /(allP aa) / rat_in_P_ge1 h.
exact: (ltr_le_trans ltr01 h).
Qed.

Lemma CF_bound a l: good_for_cf a l -> floorq a = floorq (SCF (a::l)).
Proof.
move => /and3P [ha hb hc]. 
have ap:= (all_rat_in_P_pos hb).
apply: floorp2;rewrite -(eqP ha)(SCF_pos2 _ ap) /= ltr_add2l.
move: hb hc ap; case:l => // c l hb hc /= /andP[_ ap]. 
suff ww: 1 < c + SCF' l by rewrite /= div1r invf_lt1 // (ltr_trans ltr01 ww).
move: hb => /= /andP [/rat_in_P_ge1 cp hb].
case lz: (l== [::]).  
  move:hc lz cp; clear;case: l => //= ca _ cb. 
  by rewrite addr0 ltr_neqAle eq_sym ca cb.
have la: 0 <  SCF' l by apply:SCF_pos1 =>//; rewrite lz. 
by move:(ler_lt_add cp la); rewrite addr0.
Qed.


Lemma CF_unique a a' l l' :  good_for_cf a l ->  good_for_cf a' l' ->
   SCF (a::l) = SCF(a'::l') -> a::l = a'::l'.
Proof.
wlog : a a' l l'/ (size l <= size l')%N.
   move => H; case/orP:(leq_total (size l) (size l')); first by apply: H.
   by move => ha hb hc /esym hd; symmetry; apply:H. 
move => ss ha hb sv.
move/andP: (ha) => [/eqP ha1 ha2];move/andP: (hb) => [/eqP hb1 hb2].
have aa: a = a'.
  by move: (CF_bound ha) (CF_bound hb); rewrite -sv {4}ha1 {2}hb1 => <- ->.
move:sv; rewrite aa /= => /addrI sv; congr cons.
move: ha2 hb2 ss sv; clear;elim: l l'.
  case => // a l ha /andP[ea eb] hc /= ec.
  by move:(SCF_pos1 (all_rat_in_P_pos ea) isT); rewrite /= ec ltrr.
move => a l Hrec; case; first by rewrite ltn0.
move => a' l' /= /andP[/andP[pa pb] pc] /andP[/andP[qa qb] qc].
rewrite ltnS => ss. 
move /(congr1 (fun x => 1/x)); rewrite !div1r !invrK => ee'.
have ll:(last 0 l != 1) by move: pc; case:(l).
have ll':(last 0 l' != 1) by move: qc; case:(l').
have aa: a = a'.
  have g1: (good_for_cf a l).  
     by rewrite /good_for_cf pb ll; move /andP: pa => [-> _]. 
  have g2: (good_for_cf a' l').
     by rewrite /good_for_cf qb ll'; move /andP: qa => [-> _]. 
  move:(CF_bound g1) (CF_bound g2);rewrite /= ee' => <-.
  by move /andP: qa => [/eqP {3}-> _] ->; move /andP: pa => [/eqP  <- _].
move: ee'; rewrite aa; move/addrI => ea.
congr cons; apply: Hrec => //; [by rewrite pb ll | by rewrite qb ll'].
Qed.

Lemma CF'_exists (x: rat): 0<x<1 -> 
  exists2 l, (all rat_in_P l && (last 0 l !=1)) & x = SCF' l.
Proof.
move => /andP [xp xl1].
have nqp: (0 < numq x) by rewrite (numq_gt0 x) xp.
have: `|numq x|%N = numq x :> int by rewrite abszE; move: nqp;case: (numq x).
move: (absz_denq x); set b := absz _; set a := absz _ => bv av.
have bp: (0 < b)%N by move: (denq_gt0 x); rewrite - bv; case: (b).
move: (divq_num_den x); rewrite - bv - av => xv.
case: (posnP a) => ap; first by move: xp; rewrite - xv ap mul0r. 
have: x * b%:~R < b%:~R by rewrite gtr_pmull // ltr0n.
rewrite bv - (numqE x) - bv - av ltr_int ltz_nat - xv => lab.
move: ap lab; move: (leqnn b); clear; move:a b {-2} (b) => a n b {x}.
elim: n a b. 
  by  move => a b h1 h2 h3; move: (leq_trans h3 h1); rewrite ltn0.
move => n Hrec a b lbn ap lab.
have dvde:=(divn_eq b a).
have R3:=(ltn_pmod b ap).
case: (posnP (b %/ a)) => qp.  
  by move: dvde (ltnW lab);rewrite qp mul0n add0n leqNgt=> ->; rewrite R3.
set q := (b %/ a)%:Z%:Q.
have ap':a%:Z%:Q != 0 by rewrite  intq_eq0; move: ap; case (a).
have ->: a%:~R / b%:~R = 1 / (q + (b %% a)%:~R / a%:~R).
  by rewrite - invf_div div1r {1}dvde ratN_D mulrDl ratN_M  mulfK.
have rq: rat_in_P q.
  by rewrite /q -{1} (prednK qp) rat_in_P_nat /=.
case: (posnP (b %% a)) => R2.  
  move: dvde; rewrite R2 addn0 mul0r => bv.
  exists [:: q] => //=; rewrite rq /= pnatr_eq1;case q1: (b %/ a == 1%N) => //.
  by move: lab; rewrite bv (eqP q1) mul1n ltnn.
have R1: (a <= n)%N by move: (leq_trans lab lbn); rewrite ltnS.
move: (Hrec _ _ R1 R2 R3) => [l /andP[ha hb] hc].
exists (q :: l); rewrite ? hc //= ha rq /=.
move: hb  hc;case: (l) => //= _ /eqP. 
by rewrite mulf_eq0 invr_eq0 (negbTE ap') orbF intq_eq0; move: R2; case:(b%%a).
Qed.

Lemma CF_exists (x: rat):  exists a l, good_for_cf a l /\ x = SCF (a::l).
Proof.
move: (floorp1 x) => /=; set a := (floorq x)%:~R => /andP[eq1 eq2].
have ra:  rat_in_Z a by apply: rat_in_Z_int.
have: 0 <= x - a < 1 by rewrite subr_ge0 eq1 ltr_subl_addr addrC eq2.
rewrite ler_eqVlt eq_sym subr_eq0.
case:eqP => xa /=.
  by move => _; exists a, [::]; rewrite /= addr0 /good_for_cf ra.
move /CF'_exists => [l lp xv]; exists a, l.
by rewrite /good_for_cf andbA ra lp - xv addrC addrNK.
Qed.


Fixpoint continuant (l : seq rat) :=
  if l is a :: l1 then
     if l1 is b :: l2 then a * (continuant l1) + continuant l2
     else a
  else 1.


Local Notation K := continuant.

Lemma continuantS a b l : K [:: a , b & l] = a * (K (b :: l)) + K l.
Proof. by []. Qed.

Lemma continuant2 a b : K [:: a ; b] = a * b + 1.
Proof. by []. Qed.

Lemma continuant_fib n : K (nseq n 1) = (fib n.+1)%:Z%:Q.
Proof.
elim: n {-2} (n) (leqnSn n) => [ [// | [] //] | n Hr m].
rewrite (leq_eqVlt) ltnS; case/orP; [move => /eqP -> | by apply: Hr].
have ->: (nseq n.+2 1) = [:: 1 , 1 & nseq n 1] by [].
rewrite continuantS Hr // mul1r -[(1 :: nseq n 1)]/(nseq n.+1 1) Hr //.
by rewrite - ratN_D - fibSS.
Qed.

Lemma continuant_cat l a b l' :
  K (l ++ a::b::l') = K (l ++ [::a]) * K (b::l') + K l * K l'. 
Proof.
elim: {l}(size l) {-2}l (leqnn (size l))=> [[] //= _ | n IH].
   by rewrite mul1r.
case=> [/= _|a1 [ _|b1 l]]; first by rewrite mul1r.
  rewrite !cat1s 2!continuantS; set u := K (b :: l').
  by rewrite /= mulrDl mulrDr mulrA mul1r addrAC.
rewrite ltnS -/(size _) => sLn.
rewrite !cat_cons !continuantS !mulrDl -!mulrA addrACA -mulrDr IH ?(ltnW sLn)//.
by rewrite - cat_cons IH.
Qed.

Lemma continuant_rcons a b l :
  K (rcons (rcons l b) a)  = a * K (rcons l b) + K l.
Proof.
by move: (continuant_cat l b a nil); rewrite /= mulr1 mulrC -cat_rcons !cats1.
Qed.

Lemma continuant_rev l : K (rev l) = K l.
Proof.
elim: {l}(size l) {-2}l (leqnn (size l)) =>  [[] //|n IH].
case => [// | a [// | b l]]; rewrite ltnS -/(size _) => sLn.
by rewrite !rev_cons continuant_rcons -rev_cons !IH //= ltnW.
Qed.

Lemma continuant_ge0 l: all (fun z => 0 <= z) l -> 0 <= K l.
Proof.
elim: {l}(size l) {-2}l (leqnn (size l)) =>  [[] //|n IH].
case => [// | a [| b l]]; first by rewrite /= andbT. 
rewrite continuantS ltnS -/(size _) => sLn /andP [sa sb].
apply: addr_ge0; first by apply:(mulr_ge0 sa); apply: IH.
by apply:(IH _ (ltnW sLn)); move/andP: sb => [].
Qed.

Lemma continuant_gt0 l: all (fun z => 0 < z) l -> 0 < K l.
Proof.
elim: {l}(size l) {-2}l (leqnn (size l)) =>  [[] //|n IH].
case => [// | a [| b l]]; first by rewrite /= andbT. 
rewrite continuantS ltnS -/(size _) => sLn /andP [sa sb].
apply: addr_gt0; first by apply:(mulr_gt0 sa); apply: IH.
by apply:(IH _ (ltnW sLn)); move/andP: sb => [].
Qed.

Lemma continuant_gt0_odd l: 
  all (fun z => 0 <= z) l -> ~~odd (size l) -> 0 < K l.
Proof.
elim: {l}(size l) {-2}l (leqnn (size l)) =>  [[] //|n IH].
case => [// | a  [ // | b l]]. 
rewrite continuantS ltnS -/(size _) => /ltnW sLn /andP [sa sb].
move/andP: (sb); rewrite [odd _]/= negbK => [][_ sc] os.
have: 0 <= a * K (b :: l) by apply: (mulr_ge0 sa); apply:continuant_ge0. 
by rewrite - (ler_addr (K l));apply: ltr_le_trans; apply:IH.
Qed.

Lemma continuant_zeroA l: odd (size l) ->
  (forall k, (k.*2 < size l)%N -> nth 0 l k.*2 = 0) -> K l = 0.
Proof.
elim: {l}(size l) {-2}l (leqnn (size l)) =>  [[] //|n IH].
case => [// | a  [ // | b l]]; first by move => _ _ ep /=; apply: (ep 0%N).
rewrite /size  /odd negbK -/(size _) - /(odd _) => /ltnW sa sb sc.
have az: a = 0 by apply: (sc 0%N). 
rewrite continuantS az mul0r add0r; apply: IH => // k kl. 
by move: (sc k.+1); rewrite doubleS !ltnS /=; apply.
Qed.

Lemma continuant_zeroB l: all (fun z => 0 <= z) l -> K l = 0 ->
   odd (size l) /\ (forall k, (k.*2 < size l)%N ->  nth 0 l k.*2 = 0).
Proof.
elim: {l}(size l) {-2}l (leqnn (size l)) =>  [[] //|n IH].
case => [// | a  [ // | b l]]; first by move => _ _ /= az; split => // [] [].
rewrite ltnS -/(size _) => /ltnW sa sb sc; case od: odd; last first.
  by move:(continuant_gt0_odd sb (negbT od)); rewrite sc ltrr.
move: sb; rewrite/all -/(all _ (b::l)) => /andP [sb1 sb2].
move: (sb2)=> /andP [_ sb3].
have ha: 0 <= K l by apply: continuant_ge0. 
have hb: 0 <= a * K (b :: l) by apply:(mulr_ge0 sb1); apply: continuant_ge0. 
have : 0 < K (b :: l) by apply:continuant_gt0_odd.
rewrite lt0r => /andP [knz _].
move /eqP: sc; rewrite continuantS paddr_eq0 // mulf_eq0 (negbTE knz) orbF.
move => /andP [hd /eqP /(IH l sa sb3) [_ kp]].
split => //; case=>[ | k]; first by rewrite (eqP hd).
by rewrite doubleS !ltnS => /kp.
Qed.

Lemma continuant_of0 n: K (nseq n 0) = if odd n then 0 else 1.
Proof.
elim: n {-2} (n) (leqnSn n) => [ [// | [] //] | n Hr m].
rewrite (leq_eqVlt) ltnS; case/orP; [move => /eqP -> | by apply: Hr].
have ->: (nseq n.+2 0) = [:: 0 , 0 & nseq n 0] by [].
by rewrite continuantS mul0r add0r Hr //= negbK.
Qed.

Lemma frac_continuant a l: 
   all (fun z => 0 < z) l -> SCF (a :: l) = K (a::l) / K l.
Proof.
elim: l a => [a | b l H a apl];first by rewrite /= addr0 divr1.
move: (continuant_gt0 apl); rewrite lt0r => /andP [kp _].
move/andP: apl => [_ apl].
by rewrite continuantS mulrDl mulrK // SCF_rec H // div1r invf_div.
Qed.


Fixpoint convergent_rec (f:nat -> rat) a b n :=
  if n is n1.+1 then
     if n1 is n2.+1 then 
        (f n2) * (convergent_rec f a b n1) + (convergent_rec f a b n2) 
     else b
  else a.

Definition convergent_num f := (convergent_rec f 0 1).
Definition convergent_den f := (convergent_rec f 1 0).

Definition convergent_rat f n:= 
   (convergent_num f n.+2) / (convergent_den f n.+2).

Lemma convergent_rat0 f: convergent_rat f 0 = f 0%N.
Proof.
rewrite /convergent_rat /convergent_num /convergent_den /=.
by rewrite mulr1 mulr0 addr0 add0r divr1.
Qed.

Lemma convergent_rat1 f: f 1%N != 0 -> 
   convergent_rat f 1 = SCF [:: f 0%N ; f 1%N].
Proof.
move => h.
rewrite /convergent_rat /convergent_num /convergent_den /=.
rewrite mulr1 mulr0 !addr0  add0r mulr1 mulrDl -mulrA mulrC mulrVK //.
Qed.

Lemma convergent_num_rec f n :
  convergent_num f n.+2 = 
  (f n) * (convergent_num f n.+1) + (convergent_num f n).
Proof.  by [].  Qed.

Lemma convergent_den_rec f n :
  convergent_den f n.+2 = 
  (f n) * (convergent_den f n.+1) + (convergent_den f n).
Proof.  by [].  Qed.


Lemma foo L x (n := size L):
   SCF (rcons L x) = 
    (x * (convergent_num (nth 0 L) n.+1) + (convergent_num (nth 0 L) n)) /
    (x * (convergent_den (nth 0 L) n.+1) + (convergent_den (nth 0 L) n)).
Proof.
rewrite /n; clear n. elim /last_ind: L x.
   move => x. 
   by rewrite /convergent_num /convergent_den /= mulr1 mulr0 add0r divr1.
move => L a Hrec b.
rewrite SCF_recl Hrec size_rcons convergent_num_rec convergent_den_rec.
rewrite nth_rcons ltnn eqxx.
set f1 := (nth 0 L); set f2 := (nth 0 (rcons L a)).
admit.
Abort.


End ContinuedFractions.


(** * The Fusc  function *)

Definition fusc_prop f:= 
  [/\ f 0 = 0, f 1 = 1, 
   (forall n, f (n.*2) =  f n) &
   (forall n, f (n.*2.+1) =  f n + f (n.+1)) ].


Lemma fusc_ind P:
   P 0 -> P 1 -> 
   (forall n, P n -> P (n.*2)) ->
   (forall n, P n -> P n.+1 -> P (n.*2.+1)) ->
   forall n, P n.
Proof.
move => h0 h1 he ho n.
elim: n {-2} n (leqnn n) => [ []| n Hrec [|m]] //.
rewrite ltnS -(odd_double_half m);case:(odd _).
  rewrite  add1n - doubleS => /(leq_ltn_trans (double_le1 m./2)) h. 
  by apply: he; apply: Hrec.
case: (m./2) => // k /(leq_trans (double_le3  k)) h.
by apply:ho; apply: Hrec => //; apply: ltnW.
Qed.


Lemma fusc_unique f g: fusc_prop f -> fusc_prop g -> f =1 g.
Proof.
move => [pa pb pc pd] [qa qb qc qd] n.
elim /fusc_ind: n => //.
+ by  rewrite pa qa.
+ by  rewrite pb qb.
+ by move => n h; rewrite pc qc.
+ by move => n h1 h2; rewrite pd qd h1 h2.
Qed.


(* characteristic property of the Fusc function *)

Definition fusc n :=
  let fix loop  n k :=
    if k is k'.+1 then
      if n<=1 then n else if (odd n) then (loop n./2 k') + loop (uphalf n)  k' 
      else loop n./2 k' 
    else 0
  in loop n n.

Lemma fusc_rec: fusc_prop fusc.
Proof.
set F := fix loop n k := 
    if k is k'.+1 then
      if n<=1 then n else if (odd n) then (loop n./2 k') + loop (uphalf n)  k' 
      else loop n./2 k' 
    else 0.
pose G n k := if n<=1 then n else if (odd n) then (F n./2 k) + F (uphalf n) k 
      else F n./2 k.
have Hc: forall n k, F n k = if k is k'.+1 then G n k' else 0 by move => a []. 
have aux: forall n m, n <= m -> F n n = F n m.
  move => n m le; move: {1 3 5 }n (leqnn n).
  move => p; move: p n le; elim:m; first by move => p [].
  move =>m IHm p [ _  | n]; first by case p. 
  rewrite Hc Hc /G ltnS => lenm lepn.
  have [// | le_p_n ] := leqP p 1.
  have ha: p./2 <= n by move:(leq_trans (half_le3w le_p_n) lepn); rewrite ltnS.
  rewrite (IHm _ _ lenm ha); case op: (odd p) => //;rewrite (IHm _ _ lenm) //.
  rewrite (oddE op) /= doubleK ltn_neqAle ha andbT; apply/negP; move/eqP => eq2.
  move: lepn le_p_n; rewrite (oddE op) eq2 ltnS - {2} (doubleK n) => /half_le4.
  by case n.
split => //.
  case=> // n; rewrite {+} /fusc -/F.
  by rewrite  doubleS Hc /G ltnS ltn0 - doubleS odd_double doubleK - (aux _ _ (double_le2 n)). 
case => // n;  rewrite {+} /fusc  -/F.
rewrite -/(F n.+1 n.+1) -/(F n.+2 n.+2) -/(F (n.+1).*2.+1  (n.+1).*2.+1  ).
rewrite Hc /G /odd -/odd odd_double [_ ./2 ] (uphalf_double n.+1).
rewrite [(uphalf (n.+1).*2.+1) ] (doubleK (n.+2)).
by rewrite (aux _ _ ( double_le3 n)) (aux _ _ (leqW (double_le2 n))).
Qed.


Lemma fusc0: fusc 0 = 0. Proof. by []. Qed.
Lemma fusc1: fusc 1 = 1. Proof. by []. Qed.
Lemma fusc2: fusc 2 = 1. Proof. by []. Qed.
Lemma fusc3: fusc 3 = 2. Proof. by []. Qed.

Lemma fusc_even n: fusc n.*2 = fusc n. 
Proof. by move: fusc_rec => []. Qed.
 
Lemma fusc_odd n: fusc n.*2.+1 = fusc n + fusc n.+1.
Proof. by move: fusc_rec => []. Qed.

Lemma fusc_podd n: fusc n.*2.-1 = fusc n.-1 + fusc n.
Proof. by case: n => // n; rewrite doubleS /= fusc_odd. Qed.

Lemma fusc_eq0 n: (fusc n == 0) = (n == 0).
Proof. 
elim  /fusc_ind: n => //.
  by move => n H; rewrite double_eq0 fusc_even.
by move => n h1 h2; rewrite fusc_odd addn_eq0 h1 h2 andbF. 
Qed.

Lemma fusc_gt0 n: (0 < fusc n) = (0 < n).
Proof. by rewrite !lt0n fusc_eq0. Qed.


Lemma fusc_monotone n: odd n -> n = 1 \/ fusc n.+1 < fusc n. 
Proof.
move => on; rewrite (oddE on) - doubleS fusc_even fusc_odd.
by case:(n./2) ; [ left | move => k; right; rewrite ltn_paddl // fusc_gt0 ].
Qed.

Lemma fusc_normal_rec n:
   fusc (n.+2) + ((fusc n) %% fusc (n.+1)).*2 = (fusc n) + fusc (n.+1).
Proof.
elim/fusc_ind: n => //.
  move => n _; rewrite - doubleS ! fusc_even fusc_odd addnA addnn addnC.
  by rewrite modn_small // ltn_paddr // fusc_gt0. 
by move => n H _;rewrite - doubleS fusc_even !fusc_odd - addnA modnDr H addnC.
Qed.

Lemma fusc_prevE n (P:= fun x y =>  x * ((y %/x).+1 - (y%%x==0).*2) - y%% x):
 fusc n = P (fusc n.+1)(fusc n.+2). 
Proof.
move:(fusc_normal_rec n); rewrite /P.
set A := fusc n; set B := fusc _ ; set C := fusc _.
move: (divn_eq A C); set q := A %/ C; set r :=  A %% C => eq /eqP.
have cp: 0 < C by rewrite fusc_gt0.
have rC: r < C by rewrite ltn_mod. 
have cv:= (subnK (ltnW rC)).
rewrite {1} eq addnAC -{2} cv -!addnA addnn addnA eqn_add2r => /eqP eq2.
case eq1 :(r == 0).
  move: eq eq2; rewrite (eqP eq1) addn0 subn0 - mulSnr => -> ->.
  by rewrite mulnK // modnMl mulnC subn2 !succnK subn0.
have hn: C -r < C by rewrite -{2}cv - {1}[C-r]addn0 ltn_add2l lt0n eq1.
move: (edivn_eq q hn); rewrite - eq2 edivn_def mulnC  eqn0Ngt; case => -> ->.  
by rewrite subn_gt0 rC subn0 mulSnr - addnBA ?(ltnW hn) // subKn // (ltnW rC).
Qed.

 
Lemma fuscp_injective n m:  fusc n = fusc m -> fusc n.+1 = fusc m.+1 -> n = m.
Proof.
wlog H: n m / n <= m.
 by move => H ? ?; case /orP:(leq_total n m) => sc; [ | symmetry]; apply: H.
elim: m n H => [ [] | n H] // [_ |m].
  by move => /eqP; rewrite fusc0 eq_sym fusc_eq0.
rewrite ltnS => sa sb sc; congr succn; apply: H => //.
by rewrite fusc_prevE (fusc_prevE n) sb sc.
Qed.

Lemma fusc_pow2 n: fusc (2^n) = 1.
Proof. by elim: n => [// | n IHn]; rewrite expn2S fusc_even. Qed.

Lemma fusc_succ_pow2 n: fusc ((2^n).+1) = n.+1.
Proof. 
by elim: n => [// | n IHn]; rewrite expn2S fusc_odd IHn fusc_pow2.  
Qed.

Lemma fusc_pred_pow2 n: fusc ((2^n).-1) = n.
Proof. 
by elim: n => [// | n IHn]; rewrite expn2S fusc_podd IHn fusc_pow2 addn1.
Qed.

Lemma fusc_kpow2n k n :  fusc (2 ^ n * k) = fusc k.
Proof.
by elim: n k => [k | n Hr k]; rewrite ?mul1n // expnS - mulnA mul2n fusc_even.
Qed.

Lemma fusc_palindrome i a b (p := 2 ^ i): 
   p <= a <= p.*2 ->  a + b = 3 * p -> fusc a = fusc b.
Proof.
rewrite /p => {p} sa sc.
have sb: 2 ^ i <= b <= (2 ^ i).*2.
  rewrite - (leq_add2l a) - (leq_add2l a b) sc mulSn mul2n leq_add2r addnC.
  by rewrite leq_add2l andbC.
move: sc => /eqP; elim: i a b sa sb.
  have H: forall c, 0 < c <=2 -> fusc c = 1 by case => //[][] // [].
  by rewrite expn0 => a b sa sb  _; rewrite  H // H.
move => n Hrec a b; rewrite expn2S - doubleMr.
rewrite -(odd_double_half a) -(odd_double_half b). 
case: (odd a); case: (odd b). 
+ rewrite fusc_odd fusc_odd ! leq_Sdouble !ltn_double addSn addnS - doubleD.
  rewrite - doubleS eqn_double => /andP [sa sb] /andP [sc sd] se.
  rewrite addnC (Hrec a./2 b./2.+1) ?sa ? (leqW sc) ?sd ? (ltnW sb) ? addnS //.
  by rewrite (Hrec a./2.+1 b./2) ?sc  ?(leqW sa) ?sb ? (ltnW sd) ? addSn.
+ move => _ _. 
  by rewrite addSn - doubleD => /eqP /(f_equal odd); rewrite /= !odd_double.
+ move => _ _. 
  by rewrite addnS - doubleD => /eqP /(f_equal odd); rewrite /= !odd_double.
+ rewrite fusc_even fusc_even !leq_double - doubleD eqn_double; apply: Hrec. 
Qed.

Lemma fusc_col_progression i j: j <= 2 ^ i ->
  fusc(2^ (i.+1) + j) = fusc(2 ^ i + j) + fusc j.
Proof.
elim: i j; [by case => // [] [] | move => n Hrec j].
rewrite expn2S expn2S - (odd_double_half j); case: (odd j).
  rewrite ltn_double ! addnS - !doubleD !fusc_odd addnACA => sa.
  by rewrite (Hrec _ (ltnW sa)) - addnS - addnS Hrec.
by rewrite leq_double - !doubleD ! fusc_even; apply: Hrec.
Qed.

Lemma fusc_symmetry1 i n: i <= 2^n -> fusc(2^n -i) + fusc i = fusc (2^n + i).
Proof.
case: n; first by rewrite leqn1; case/orP => /eqP -> //.
move => n l1; set p := 2^n;case/orP:(leq_total i p) => l2.
  have ha: p <= i + p <= p.*2 by rewrite leq_addl - addnn leq_add2r.
  have hb: i + p + (2 ^ n.+1 - i) =  3*p.
    rewrite expn2S -addnn -/p - addnBA // addnC - addnA (addnA _ i) subnK //.
    by rewrite addnn -mul2n -mulSn.
  by rewrite -(fusc_palindrome ha hb) fusc_col_progression // (addnC p).
move: (subnKC l1); set j := _ - _ => l3.
have l4: j <= 2^n by rewrite - (leq_add2l i) l3 expn2S - addnn leq_add2r.
have ha : p <= i <= p.*2 by rewrite /p -expn2S l1 l2.
have hb: i + (j +p) = 3 *p by rewrite addnA l3 mulSnr expn2S mul2n.
have hc:  2 ^ (n.+1) <= 2 ^ n.+1 + i <= (2 ^ (n.+1)).*2.
  by rewrite leq_addr - addnn leq_add2l.
rewrite (fusc_palindrome ha hb) addnC (addnC j) - fusc_col_progression //.
by symmetry;apply:(fusc_palindrome hc);rewrite addnACA l3 addnn -mul2n -mulSnr.
Qed.

Lemma fusc_bound i n: i <= 2 ^n ->
  fusc i <= fusc (2 ^ n + i) ?= iff (i == 2 ^ n).
Proof.
move => h; rewrite -(fusc_symmetry1 h).
apply/leqifP; case hb: (i == 2 ^ n);first by rewrite (eqP hb) subnn add0n eqxx.
by apply/ltn_paddl; rewrite lt0n fusc_eq0 - lt0n subn_gt0  ltn_neqAle h hb.
Qed.

Lemma fusc_lower_bound  n:  n.*2 < 2 ^ fusc n.*2.+1.
Proof. 
have T k: k != 0 -> 1 < 2 ^ (fusc k).
  by rewrite -[1]/(2^0) ltn_exp2l // lt0n fusc_eq0.
elim /fusc_ind :n => //.
  move => n H; rewrite fusc_odd expnD fusc_even; case nz: (n == 0).
     by rewrite (eqP nz).
  apply: (@leq_trans (2 * 2 ^ fusc n.*2.+1)); first by rewrite mul2n ltn_double.
  by rewrite leq_pmul2r ? expn_gt0 // T // nz.  
case => // n H _.
rewrite fusc_odd expnD - doubleS fusc_even.
apply: (@leq_trans (2 ^ fusc (n.+1).*2.+1 * 2)).
  rewrite muln2 ltn_double - doubleS; move: H; case: (fusc (n.+1).*2.+1) => //.
  by move => m; rewrite expn2S ltn_double leq_double.
rewrite leq_pmul2l ? expn_gt0 // T //. 
Qed.

(* Coprimality *)
Lemma fusc_coprime n: coprime (fusc n) (fusc n.+1).
Proof.
elim /fusc_ind:n; [ done | done | move => n H | move => n H _].
  by rewrite fusc_even fusc_odd /coprime gcdnDl.
by rewrite - doubleS fusc_even fusc_odd /coprime gcdnC gcdnDr gcdnC.
Qed.


Lemma fusc_coprime_palindrome  i a b (p := 2 ^ i): 
   p <= a <= p.*2 -> (a + b).+1 = 3 * p -> coprime (fusc a)(fusc b).
Proof.
rewrite -addnS => sa sb. 
by rewrite (fusc_palindrome sa sb) coprime_sym; apply:fusc_coprime.
Qed.


(* alternate proof *)
Lemma fusc2_injective n m:  fusc n = fusc m -> fusc n.+1 = fusc m.+1 -> n = m.
Proof.
wlog H: n m / n <= m.
   move => Hrec sa sb; case /orP:(leq_total n m) => sc; first by apply: Hrec.
   symmetry; apply: Hrec => //.
have aux a b c: b +a + c = a -> (b==0) && (c == 0).
  by rewrite (addnC b) -addnA -{2} (addn0 a) - addn_eq0 - (eqn_add2l a) => /eqP.
elim /fusc_ind: m n H => [n | n | n Hrec m | n Hrec _ m].
+ by rewrite leqn0 => /eqP.
+ rewrite leq_eqVlt; case/orP; first by move/eqP => ->.
  by rewrite /fusc ltnS leqn0 => /eqP -> /=.
+ rewrite - (odd_double_half m); case: (odd m);
     rewrite - ?doubleS !fusc_even !fusc_odd. 
    by move => _ <- /esym /aux; rewrite !fusc_eq0 andbF.
  rewrite leq_double => /Hrec h1 h2 /eqP;rewrite h2 eqn_add2l => /eqP h3.
  by rewrite h1.
+ rewrite - (odd_double_half m); case: (odd m);
      rewrite - !doubleS !fusc_even !fusc_odd. 
    rewrite ltnS leq_double => /Hrec h1 /eqP h2 h3. 
    by move: h2; rewrite h3 eqn_add2r => /eqP h2; rewrite h1.
  by move => _ -> /aux;rewrite !fusc_eq0 andbF.
Qed.


Lemma fusc_bezout
   (a := fun  n =>fusc (2^log2 n - n))
   (c := fun n => if (n== 2^(log2 n).-1) then 0 else a n):
   (forall n,  (c n.+1) * (fusc n) + 1 = (a n) *(fusc n.+1)).  
Proof.
have Ha0: a 0 = 1 by [].
have Hb0: c 1 = 0 by [].
have Hae: (forall n, a (n.*2) = a n).
  by case => // n;rewrite /a log2_double expn2S - doubleB fusc_even.
have Hbe: (forall n, c (n.*2) = c n).
  case => // n.  
  by rewrite /c log2_double Hae succnK {1} log2S_k expn2S eqn_double.
have Hao:  (forall n, a (n.*2.+1) = a n + c n.+1).
  have exps k: (2^k).-1.+1 = 2^k by apply:prednK; rewrite expn_gt0.
  move => n; rewrite /c;move:(log2_bnd n) =>/andP[];rewrite leq_eqVlt eq_sym.
  case: eqP => eqa /= ha hb.
    have aux k: a ((2^k ).-1) = 1. 
      by rewrite /a log2_pred_pow - {1} exps subSn // subnn.
    set k := (log2 n.+1).-1.
    have eqb: n = (2^k ).-1 by rewrite /k - eqa succnK. 
    by rewrite eqb aux - (succnK (_.+1)) - doubleS exps - expn2S  aux.
  rewrite /a.
  set k :=(log2 n.+1).-1.
  have: log2 n = k.+1 by apply:log2_pr;rewrite -ltnS ha /k -log2S_k (ltnW hb).
  move => ea; move: hb; rewrite log2_Sdouble ea log2S_k -/k => /ltnW hb.
  move:(subnK hb) (subnK (ltnW hb)); rewrite subnS; set x := _ - _ => sa sb.
  rewrite expn2S -addnn -addnn -addnS subnDA - (addnBA _ (ltnW hb)) addnC. 
  rewrite - addnBA // subnS -/x; case x => //m. 
  by rewrite succnK addSn addnn fusc_odd addnC.
have Hbo: (forall n, c (n.*2.+3) = a n.+1 + c n.+2).
  move =>n; rewrite -(Hao n.+1) /c doubleS;case: eqP => //. 
  case:((log2 n.*2.+3).-1) => //n1 h; move: (f_equal odd h).  
  by rewrite expn2S /= !odd_double.
elim /fusc_ind.
+ by rewrite muln0 Ha0.
+ move: (Hao 0)(Hbe 1); rewrite Ha0 Hb0 => -> -> //.
+ move => n Hr; rewrite fusc_even fusc_odd Hae  mulnDr -Hr addnA  - mulnDl.
  by case n; [rewrite !muln0 | move => k; rewrite doubleS Hbo].
+ move => n Hr _.
  by rewrite Hao -doubleS Hbe fusc_even fusc_odd mulnDl mulnDr - Hr addnAC.
Qed.

Lemma fusc_bezout2 i n: i < 2^n ->
  fusc (2 ^ n + i) * fusc i.+1 = 1 + fusc (2 ^ n + i.+1) * fusc i.
Proof.
elim /fusc_ind: i n.
+ by move => n; rewrite fusc0 fusc1 addn0 addn1 fusc_pow2 fusc_succ_pow2 muln0.
+ move => n;rewrite fusc1 fusc2 ! muln1 addn1 fusc_succ_pow2; case: n => //.
  by move => n _; rewrite expn2S addn2 -doubleS fusc_even fusc_succ_pow2 add1n.
+ move => i H; case.
     rewrite expn0 ltnS (leq_double i 0) leqn0 => /eqP -> //.
  move =>n; rewrite expn2S ltn_double addnS -doubleD !fusc_even !fusc_odd => ha.
  by rewrite mulnDr mulnDl H // addnCA addnS.
+ move => i Ha Hb; case; first by rewrite ltnS ltn0.
  move => n. rewrite expn2S ltn_Sdouble !addnS - doubleD -!doubleS => ha.
  by rewrite !fusc_even !fusc_odd mulnDr mulnDl Ha // addnS addnA.
Qed.

Section SternRat.

Local Open Scope ring_scope.

Definition Sba_p (x: rat) := 1 + x.
Definition Sba_i (x: rat) := (1 + x^-1)^-1.
Definition Sba_m (x: rat) := x - 1.
Definition Sba_j (x: rat) := (x^-1 - 1)^-1.

Lemma Sba_i_prop x: x != 0 -> Sba_i x = x /(1 + x).
Proof. 
by move => xnz; rewrite /Sba_i -(div1r x) addf_div1 // invf_div. 
Qed.

Lemma Sba_j_prop x: x != 0 -> Sba_j x = x /(1 - x).
Proof. 
by move => xnz; rewrite /Sba_j -(div1r x) subf_div2 // invf_div.
Qed.

Lemma Sba_pK: cancel Sba_p Sba_m.
Proof. by move => x; rewrite /Sba_p /Sba_m addrAC subrr add0r. Qed.

Lemma Sba_mK: cancel Sba_m Sba_p.
Proof. by move => x; rewrite /Sba_m /Sba_p addrCA subrr addr0. Qed.

Lemma Sba_iK: cancel Sba_i Sba_j.
Proof. 
move => x.
case xnz: (x == 0); first by rewrite /Sba_i/Sba_j (eqP xnz) invr0.
have eq0: x = (1 + x) -1 by rewrite addrAC subrr add0r.
rewrite (Sba_i_prop (negbT xnz)).  
case h:(1 + x == 0). 
  by rewrite {3} eq0  (eqP h) /Sba_j invr0 mulr0 - div1r. 
rewrite Sba_j_prop.
   rewrite  subf_div1 ?h //.
   by rewrite - addrA subrr addr0 - mulf_div divr1 divff ?mulr1 // invr_eq0 h.
by rewrite mulf_eq0 xnz invr_eq0 h.
(* orig 
rewrite Sba_j_prop ?mulf_eq0 ?xnz ?invr_eq0 ?h // subf_div1 ? h//.
by rewrite - addrA subrr addr0 - mulf_div divr1 divff  ?invr_eq0 ?h // mulr1.
*) 
Qed.

Lemma Sba_jK: cancel Sba_j Sba_i.
Proof. 
move => x.
case xnz: (x == 0); first by rewrite /Sba_i/Sba_j (eqP xnz) invr0.
have eq0: x = 1 - (1 - x) by rewrite opprB addrCA subrr addr0.
rewrite Sba_j_prop  ? xnz //.  
case h:(1 - x == 0); first by rewrite {3} eq0 (eqP h) /Sba_i invr0 mulr0.
have h':1 - x != 0 by rewrite h.
(* ORIG
rewrite Sba_i_prop ?mulf_eq0 ?xnz ?invr_eq0 // addf_div1 // {2} (addrC 1).
by rewrite addrA subrr add0r - mulf_div divr1 divff  ?invr_eq0  // mulr1.
*)
rewrite Sba_i_prop.
  rewrite (addf_div1 _ h') {2} (addrC 1).
  by rewrite addrA subrr add0r - mulf_div divr1  divff ?mulr1 // invr_eq0 . 
by rewrite mulf_eq0 xnz invr_eq0 h.
Qed.

Lemma Sba_mjK x: (Sba_j x) ^-1 = (Sba_m x^-1).
Proof. by rewrite /Sba_m /Sba_j invrK /Sba_i. Qed.


Lemma Sba_p_pos x: 0 < x -> 1 < (Sba_p x).
Proof. by move => h; rewrite /Sba_p -ltr_subl_addl. Qed.

Lemma Sba_m_pos x: 1 < x -> 0 < (Sba_m x).
Proof. by move => h; rewrite /Sba_m subr_gt0.  Qed.
 
Lemma Sba_m_pos_contra x: 0 < x -> {y:rat | (1 < y) && (Sba_m y == x) }.
Proof.
by move => h; exists (Sba_p x); rewrite Sba_pK eqxx andbT Sba_p_pos. 
Qed.

Lemma Sba_j_pos x: 0 < x < 1 -> 0 < (Sba_j x).
Proof. 
by move => /andP[h1 h2]; rewrite /Sba_j invr_gt0 subr_gt0 invf_gt1.
Qed.

Lemma Sba_i_pos x: 0 < x -> 0 < Sba_i x < 1.
Proof.
move => h.
have h1: 1 < 1 + x^-1 by apply: Sba_p_pos; rewrite invr_gt0.
by move: (ltr_trans ltr01 h1) => h2; rewrite invr_gt0  invf_lt1 h2. 
Qed.

Lemma Sba_j_pos_contra x: 0 < x -> {y:rat | (0 < y <1) && (Sba_j y == x) }.
Proof.
move => h; exists (Sba_i x); rewrite Sba_iK eqxx andbT; exact:Sba_i_pos.
Qed.


Definition snumden' x := numq x + denq x.
Definition snumden x := `|snumden' x|.-1.

Lemma snumden_pos' x:  0 <= x -> 0 < snumden' x.
Proof. 
rewrite le0r => /orP; case; first by move/eqP ->.
by rewrite /snumden' -numq_gt0 => h; apply: addr_gt0. 
Qed.

Lemma snumden_pos x: 0 <=x -> snumden' x = (snumden x).+1.
Proof.
by move/snumden_pos'; rewrite /snumden; case: (snumden' x) => // [][]. 
Qed.


Lemma snumden_gt0 x: 0 < x ->  (snumden x) != 0%N.
Proof.
move => xp; apply /negP => h.
move: (snumden_pos (ltrW xp)); rewrite (eqP h) /snumden' => eq1.
move:xp (denq_gt0 x); rewrite - numq_gt0 ! gtz0_ge1 => sa sb.
by move: (ler_add sa sb); rewrite eq1. 
Qed.

Lemma snumden_inv x:  0 < x  -> snumden x = snumden (x^-1).
Proof.
rewrite /snumden/snumden' -numq_gt0 -div1r; case/ratP:x => n d. 
rewrite div1r invf_div addrC coprime_sym =>cp np.
rewrite coprimeq_num // coprimeq_den // gtr0_sg // mul1r gtr0_norm //.
by move: np; rewrite lt0r => /andP [ /negbTE -> _].
Qed.

Lemma Sba_m_snum x: 1 < x ->  (snumden (Sba_m x) <  snumden x)%N.
Proof.
suff: 1 <x -> snumden' (Sba_m x) <  snumden' x.
  move => H x1; move: (H x1).
  rewrite (snumden_pos(ltrW(Sba_m_pos x1))).
  by rewrite (snumden_pos(ltrW (ltr_trans ltr01 x1))).
rewrite /Sba_m -subr_gt0 -{3} (subrK 1 x) -numq_gt0 /snumden /snumden'.
case/ratP: (x-1) => n d cp n0.
have H: coprime `|n + d.+1| d.+1.
  by rewrite - (gtz0_abs n0) - PoszD /= /coprime gcdnC gcdnDr gcdnC.
rewrite (addrC _ 1) addf_div1 ?intr_eq0 //- intrD coprimeq_den //.
by rewrite coprimeq_num // sgrEz /= gtr0_sgz // mul1r ltr_addl normr_gt0.
Qed.


Lemma Sba_j_snum x: 0 < x <1 ->  (snumden (Sba_j x) <  snumden x)%N.
Proof.
move => H; have h1:= (Sba_j_pos H); move/andP:H => [ha hb]. 
by rewrite (snumden_inv h1) Sba_mjK (snumden_inv ha) Sba_m_snum // invf_gt1. 
Qed.

Fixpoint Stern_bij_rec (x:rat) (n:nat) :=
  if n is m.+1 then
    if(0 < x < 1) then xO (Stern_bij_rec (Sba_j x) m)
    else if(1 < x) then xI (Stern_bij_rec (Sba_m x) m)
    else xH
  else xH.
Definition Stern_bij1 x :=  Stern_bij_rec x (snumden x).+1.
Definition Stern_bij x := if (x<=0) then 0%N else nat_of_pos(Stern_bij1 x). 



Lemma Stern_bij_recE (x:rat) n : 0 < x -> ((snumden x) < n)%N ->
  Stern_bij_rec x n  = Stern_bij1 x.
Proof.
elim: n {-2} n (leqnn n) x => [[] | n Hr k] //.
rewrite leq_eqVlt ltnS; case /orP; last by move => le; apply: Hr.
move /eqP -> => x xp; rewrite ltnS => le2.
have Hb z: (z < snumden x -> z < n)%N by move => h; exact: (leq_trans h le2).
case: (ltrgtP x 1) => lx1.
+ have ll: 0 < x < 1 by rewrite xp lx1.
  move:(Sba_j_pos ll) (Sba_j_snum ll) => sa sb; move:(Hb _ sb) => sc.
  by rewrite /= ll Hr // {2} /Stern_bij1 /= ll Hr.
+ have ll: (0 < x < 1) = false by rewrite xp ltrNge (ltrW lx1).
  move:(Sba_m_pos lx1) (Sba_m_snum lx1) => sa sb; move:(Hb _ sb) => sc.
  by rewrite /= ll lx1  Hr // {2} /Stern_bij1 /= ll lx1 Hr.
+ by rewrite lx1.
Qed.

Lemma Stern_bij1_1: Stern_bij1 1 = 1%positive.  
Proof. by []. Qed.


Lemma Stern_bij1_lt1 x : 0 < x < 1 ->  
   Stern_bij1 x = xO (Stern_bij1 (Sba_j x)).
Proof.
move => xp1; rewrite -(Stern_bij_recE (Sba_j_pos xp1) (Sba_j_snum xp1)).
by rewrite /Stern_bij1 /= xp1.  
Qed.

Lemma Stern_bij1_gt1 x : 1 < x ->  Stern_bij1 x = xI (Stern_bij1 (Sba_m x)).
Proof.
move => xp1; rewrite - (Stern_bij_recE (Sba_m_pos xp1) (Sba_m_snum xp1)).
by rewrite {1} /Stern_bij1 /= (ltrNge x 1) (ltrW xp1) andbF xp1.
Qed.

Lemma Stern_bij1_lt1K x : 0 < x -> 
  Stern_bij1 (Sba_i x) = xO (Stern_bij1 x).
Proof. by move /Sba_i_pos /Stern_bij1_lt1; rewrite Sba_iK. Qed.

Lemma Stern_bij1_gt1K x : 0 < x -> 
  Stern_bij1 (Sba_p x) = xI (Stern_bij1 x).
Proof. by move /Sba_p_pos /Stern_bij1_gt1;rewrite Sba_pK. Qed.

Lemma Stern_bij_0: Stern_bij 0 = 0%N.  
Proof. by []. Qed.

Lemma Stern_bij_1: Stern_bij 1 = 1%N.  
Proof. by rewrite /Stern_bij Stern_bij1_1. Qed.


Lemma Stern_bij_lt1 x : 0 < x < 1 ->  
   Stern_bij x =  (Stern_bij (Sba_j x)).*2.
Proof.
move => h.
move/andP: (h) => [xp _].
move: (Stern_bij1_lt1 h).
rewrite /Stern_bij ! lerNgt (Sba_j_pos h) xp /negb => -> /=.
by rewrite natTrecE.
Qed.  (* ORIG *)




Lemma Stern_bij_gt1 x : 1 < x ->  
   Stern_bij x = (Stern_bij (Sba_m x)).*2.+1.
Proof.
move => h.
move:(Stern_bij1_gt1 h);rewrite /Stern_bij ! lerNgt  (Stern_bij1_gt1 h). 
by rewrite (Sba_m_pos h) (ltr_trans ltr01 h) /= natTrecE.
Qed.

Lemma Stern_bij_lt1K x : 0 < x -> 
  Stern_bij (Sba_i x) = (Stern_bij x).*2.
Proof. by move /Sba_i_pos /Stern_bij_lt1; rewrite Sba_iK. Qed.


Lemma Stern_bij_gt1K x : 0 < x -> 
  Stern_bij (Sba_p x) = (Stern_bij x).*2.+1.
Proof. by move /Sba_p_pos /Stern_bij_gt1;rewrite Sba_pK. Qed.


Lemma Stern_bij1_surj p: { x | (0 < x) /\ (Stern_bij1 x = p) }.
Proof.
elim: p => [ p [x [xp ev]] |  p [x [xp ev]] | ].
+ move: (ltr_trans ltr01 (Sba_p_pos xp)) => lt2.
  by exists (Sba_p x); rewrite Stern_bij1_gt1K // ev. 
+ move: (Sba_i_pos xp) => /andP [lt1 _].
  by exists  (Sba_i x); rewrite Stern_bij1_lt1K // ev.   
by exists 1.
Qed.

Lemma Stern_bij_surj n: { x | (0 <= x) /\ (Stern_bij x = n) }.
Proof.
case: n; first by exists 0.
move => n; move:(Stern_bij1_surj (pos_of_nat n n)) => [x [xp xv]].
exists x; split; first by apply: ltrW.
rewrite /Stern_bij xv lerNgt xp /=; exact:(bin_of_natK n.+1).
Qed.

Lemma Stern_bij1_inj  x y: 0 < x -> 0 < y  ->
  Stern_bij1 x = Stern_bij1 y -> x = y.
Proof.
move: (leq_maxl (snumden x) (snumden y)) (leq_maxr (snumden x) (snumden y)).
move: (maxn _ _) => k; elim: k x y => [ x y | n Hrec x y].
  by rewrite leqn0 => sa _ /snumden_gt0; rewrite sa.
wlog lexy: x y / x <= y.
   move => H l1 l2 xp yp eq; case /orP: (ler_total x y) => l3;first by apply:H.
   by symmetry; apply: H.
move => lxn lyn xp yp.
case:(ltrgtP 1 x) => cx1.
+ have l1y := (ltr_le_trans cx1 lexy).
  rewrite (Stern_bij1_gt1 cx1) (Stern_bij1_gt1 l1y); case => eq'.
  rewrite - (Sba_mK x) - (Sba_mK y).
  move:(Sba_m_pos cx1) (Sba_m_pos l1y) => xp' yp'.
  move: (leq_trans (Sba_m_snum cx1) lxn) (leq_trans(Sba_m_snum l1y) lyn).
  by rewrite !ltnS => lxn' lyn'; rewrite (Hrec _ _ lxn' lyn' xp' yp' eq').
+ have lx1 : 0 < x < 1 by rewrite xp cx1.
  case :(ltrgtP 1 y) => cy1.
  * by rewrite (Stern_bij1_gt1 cy1)  (Stern_bij1_lt1 lx1).
  * have ly1 : 0 < y < 1 by rewrite yp cy1.
    rewrite (Stern_bij1_lt1 ly1)  (Stern_bij1_lt1 lx1); case => eq'.
    rewrite -(Sba_jK x) -(Sba_jK y).
    move:(Sba_j_pos lx1) (Sba_j_pos ly1) => xp' yp'.
    move: (leq_trans (Sba_j_snum lx1) lxn) (leq_trans(Sba_j_snum ly1) lyn).
    by rewrite !ltnS => lxn' lyn'; rewrite (Hrec _ _ lxn' lyn' xp' yp' eq').
  * by rewrite - cy1 Stern_bij1_1  (Stern_bij1_lt1 lx1).
+ rewrite - cx1; case y1: (y==1); first by rewrite  (eqP y1).
  have l1y: 1 < y by rewrite ltr_neqAle; rewrite eq_sym y1 cx1.
  by rewrite Stern_bij1_1  (Stern_bij1_gt1 l1y). 
Qed.

Lemma Stern_bij_gt0 x: 0 < x -> (0 < Stern_bij x)%N.
Proof. 
by rewrite /Stern_bij lerNgt => -> /=; rewrite lt0n nat_of_pos_ne0.
Qed.


Lemma Stern_bij_inj  x y: 0 <= x -> 0 <= y  ->
  Stern_bij x = Stern_bij y -> x = y.
Proof.
have H w: (0 < w) ==> (Stern_bij w != 0)%N.
  by rewrite - lt0n; apply/implyP/Stern_bij_gt0.
move => sa sb sc;move:sa sb sc (H x)(H y).
rewrite /Stern_bij; case: (ltrgt0P x) => //; case: (ltrgt0P y) => //.
+ by move => xp yp _ _ / nat_of_pos_inj/Stern_bij1_inj h _ _; apply h.
+ by move => _ _ _ _ ->. 
+ by move => _ _ _ _ <-. 
+ by move => -> ->.
Qed.



(*  Quotient of fusc *)

Definition Stern n := (fusc n)%:Q  / (fusc n.+1)%:Q. 

Lemma Stern0: Stern 0 = 0. Proof. by []. Qed.
Lemma Stern1: Stern 1 = 1.  Proof. by [].  Qed.
Lemma Stern2: Stern 2 = 1/2%:Q.  Proof. by [].  Qed.


Lemma Stern_ge0 n: 0 <= Stern n.
Proof. apply:divr_ge0; apply: ler0n. Qed.

Lemma Stern_gt0 n: 0 < Stern n.+1.
Proof. by apply:divr_gt0; rewrite ltr0n fusc_gt0. Qed.

Lemma Stern_nz n: Stern n.+1 != 0.
Proof. by move:(Stern_gt0 n); rewrite ltr_def => /andP[]. Qed.


Lemma Stern_pow2 n: Stern (2^n) = 1/(n.+1)%:Q.
Proof. by rewrite /Stern fusc_pow2 fusc_succ_pow2. Qed.

Lemma Stern_pred_pow2 n: Stern ((2^n).-1) = n%:Q.
Proof. 
move: (expn_gt0 2 n) => /= /prednK eq.
by rewrite /Stern eq fusc_pow2 fusc_pred_pow2 divr1.
Qed.

Lemma Stern_even n: Stern ((n.+1).*2) = Sba_i (Stern (n.+1)).
Proof.
rewrite /Stern /Sba_i fusc_even fusc_odd ratN_D [X in 1 + X] invf_div.
(* ORIG 
  by rewrite addrC addf_div1 ? div1r ? invf_div // pnatr_eq0 fusc_eq0. *)
rewrite addrC addf_div1; first by rewrite [in RHS] invf_div.
by rewrite pnatr_eq0 fusc_eq0.
Qed.

Lemma Stern_odd n: Stern (n.*2.+1) = Sba_p (Stern n).
Proof.
rewrite /Stern /Sba_p /= - doubleS fusc_even fusc_odd  ratN_D addf_div1 //.
by rewrite  pnatr_eq0 fusc_eq0.
Qed.


Lemma Stern_palindrome a: (0 < a)%N ->
  (Stern a)^-1 = Stern ((3* 2^(log2 a).-1 -a).-1).
Proof.
case: a => // a _. 
move: (log2_bnd a) => /andP[]; rewrite {2}log2S_k.
set n := (log2 a.+1).-1; set b :=  _.-1; move => sa sb.
have eb: b = ((2 ^ n.+1 - a.+2) + 2^n)%N.
  by rewrite /b -subnS mulSn - expnS - addnBA // addnC.
rewrite expn2S in sb.
have sc: (2^n <= b)%N by rewrite eb; apply: leq_addl.
have sd: (b < (2^n).*2)%N by rewrite eb expn2S -{2}(subnK sb) ltn_add2l ltnS.
have Ha: (2 ^ n <= a.+2 <= (2 ^ n).*2)%N by rewrite (leqW sa) sb.
have Hc: (2 ^ n <= a.+1 <= (2 ^ n).*2)%N by rewrite sa (ltnW sb).
have eab:(a.+2 + b = 3 * 2 ^ n)%N. 
   by rewrite eb addnA expn2S (subnKC sb) -muln2 -mulnSr mulnC.
rewrite /Stern (fusc_palindrome Ha eab). 
by rewrite addSnnS in eab; rewrite(fusc_palindrome Hc eab) invf_div.
Qed.

Lemma Stern_numden n: 
   (numq(Stern n) == fusc n)  && (denq (Stern n) == fusc n.+1).
Proof.
move: (fusc_coprime n). 
rewrite - {1} (absz_nat (fusc n)) - (absz_nat (fusc n.+1)) => H.
rewrite (coprimeq_den H) (coprimeq_num H) eqz_nat sgrEz.  
by rewrite gtr0_sgz ? gtr0_sgz ? ltz_nat  ? lt0n  fusc_eq0 //=  mul1r // !eqxx.
Qed.


Lemma Stern_injective: injective Stern.
Proof.
move => n m eq1.
move: (Stern_numden n) (Stern_numden m) => /andP [/eqP e1 /eqP e2] /andP[e3 e4].
by apply: fusc2_injective;  apply /eqP; rewrite - eqz_nat -?e1 - ?e2 eq1.
Qed.

(* see stern_bijK below *)

Lemma Stern_surjective x: 0 <= x -> {n | x = Stern n}.
Proof.
move => h; exists (Stern_bij x); move:h.
rewrite le0r; case/orP;first by move/eqP ->;rewrite Stern_bij_0 Stern0.
move: (leqnn (snumden x)); rewrite - ltnS; move:{2} (_ .+1) => k. 
elim :k x  => // n Hx x le1 xp.
have Hb z: (z < snumden x -> z < n)%N by move => h; exact: (leq_trans h le1).
case :(ltrgtP x 1) => lx1.
  have ll: 0 < x < 1 by rewrite xp lx1.
  have pa:=(Sba_j_pos ll).  
  rewrite (Stern_bij_lt1 ll) - {1} (Sba_jK x).
  move: (Hx _ (Hb _ (Sba_j_snum ll)) pa). 
  by rewrite - (prednK(Stern_bij_gt0 pa))  Stern_even => <-.
+ rewrite (Stern_bij_gt1 lx1) Stern_odd.
  by rewrite - (Hx _ (Hb _ (Sba_m_snum lx1)) (Sba_m_pos lx1)) Sba_mK.
+ by rewrite lx1 Stern_bij_1 Stern1.
Qed.


Lemma SternK: cancel Stern Stern_bij.
Proof.
elim/fusc_ind.
+ by rewrite Stern0 Stern_bij_0.
+ by rewrite Stern1 Stern_bij_1.
+ case; first by rewrite Stern0 Stern_bij_0.
  by move => n Hrec; rewrite Stern_even - {2} Hrec Stern_bij_lt1K // Stern_gt0.
+ case; first by rewrite Stern1 Stern_bij_1.
  by move => n Hrec _; rewrite -{2} Hrec Stern_odd Stern_bij_gt1K  // Stern_gt0.
Qed.

Lemma Stern_bijK x: 0 <= x -> x = Stern (Stern_bij x).
Proof.
move => h.
by move: (Stern_bij_inj (Stern_ge0 (Stern_bij x)) h (SternK (Stern_bij x))).
Qed.

Lemma fusc_pair_surj a b: coprime a b.+1 -> 
   {n | a = fusc n /\ b.+1 = fusc n.+1 }.
Proof.
rewrite - {1} (absz_nat a) - (absz_nat (b.+1)) => H.
set x := (a)%:Q  / (b.+1)%:Q. 
have: 0 <= x by apply:divr_ge0; rewrite ler0n.
move /Stern_surjective => [n eqx]; move: (Stern_numden n).
rewrite - eqx /x (coprimeq_den H)(coprimeq_num H) sgrEz gtr0_sgz // mul1r.
by rewrite !eqz_nat //=;move/andP => [/eqP -> /eqP ->]; exists n.
Qed.

(* ORIG
Lemma Stern_next n: Stern_succ_fct (Stern n) = Stern (n .+1).
Proof.
have Ha k: 0 < (fusc k.+1)%:Z by rewrite ltz_nat fusc_gt0.
have Hb k: (fusc (k.+1))%:Q != 0  by rewrite intr_eq0 eqz_nat fusc_eq0.
rewrite - (odd_double_half n); case: (n./2); case: {n} (odd n)=> // m. 
  rewrite Stern_odd -doubleS Stern_even /Stern /Sba_p /Sba_i.
  rewrite  invf_div addf_div1 // addf_div1 // invf_div Sn_gt1 // addrC.
  move: (f_equal Posz (fusc_normal_rec m.+1)); rewrite - addnn !PoszD - mulz2. 
  by move => <-; rewrite - addrA - mulrBl modz_nat subrr mul0r addr0.
rewrite Stern_even Stern_odd  /Stern /Sba_i /Sba_p invf_div addf_div1 //.
rewrite addf_div1 // addrC invf_div Sn_lt1 //.
Qed.
*)

Lemma Stern_next n: Stern_succ_fct (Stern n) = Stern (n .+1).
Proof.
have Ha k: 0 < (fusc k.+1)%:Z by rewrite ltz_nat fusc_gt0.
have Hb k: (fusc (k.+1))%:Q != 0  by rewrite intr_eq0 eqz_nat fusc_eq0.
rewrite - (odd_double_half n); case: (n./2); case: {n} (odd n)=> // m. 
  rewrite Stern_odd -doubleS Stern_even /Stern /Sba_p /Sba_i.
  rewrite [X in (1 + X) ^-1] invf_div addf_div1 // addf_div1 // invf_div Sn_gt1 // addrC.
  move: (f_equal Posz (fusc_normal_rec m.+1)); rewrite - addnn !PoszD - mulz2. 
  by move => <-; rewrite - addrA - mulrBl modz_nat subrr mul0r addr0.
rewrite Stern_even Stern_odd  /Stern /Sba_i /Sba_p  [X in (1 + X) ^-1]  invf_div  addf_div1 //.
rewrite addf_div1 // addrC invf_div Sn_lt1 //.
Qed.

Lemma Stern_prev n: Stern_prev_fct (Stern n.+1) = Stern n.
Proof. by move:(Stern_succ_fctK (Stern n)); rewrite Stern_next. Qed.

End SternRat.


Lemma fusc_middle_div k q  (n := 2^k * (q.*2.+1)):
    fusc (n.-1) + (fusc n.+1) = (k.*2.+1) * fusc n.
Proof.
rewrite /n {n}; elim: k.
   by rewrite expn0 mul1n /= - doubleS fusc_odd !fusc_even // mul1n.
move => n.
rewrite expnS - mulnA mul2n /= fusc_even fusc_odd. 
rewrite fusc_podd ? muln_eq0 ?expn_eq0 //; set t:= _*_.
rewrite (addnC (fusc t)) addnACA => ->.
by rewrite addnn - (mul2n (fusc t)) -mulnDl addn2 mulSn.
Qed.

Lemma fusc_is_even n: (odd (fusc n)) = (n %%3 !=0). 
Proof.
have lt3 : 0 < 3 by [].
elim/fusc_ind:n => //.
  move => n Hr; rewrite fusc_even Hr -addnn - modnDm.
  by move: (ltn_pmod n lt3); case (n %% 3) => // [] [] // [].
move => n Hr1 Hr2; rewrite fusc_odd odd_add Hr1 Hr2 -addnn -addnS -modnDm.
rewrite - (add1n n) - modnDm.
move: (ltn_pmod n lt3); case (n %% 3) => // [] [] // [] //.
Qed.

Lemma fusc_is_even1 n: fusc n + fusc n.+2 = fusc (n.+1) %[mod 2].
Proof.
case: (elogn2P n) => k q eq.
move:(fusc_middle_div k q) => /=; rewrite -eq succnK => ->.
by rewrite - modnMm  -add1n -modnDm /= -muln2 modnMl addn0 // mul1n modn_mod.
Qed.

Lemma fusc_coprime1 n: fusc n + fusc n.+2 = fusc (n.+1) -> 
  coprime (fusc n) (fusc n.+2).
Proof.
case: (elogn2P n) => k q ea.
move:(fusc_middle_div k q) => /=; rewrite -ea succnK => -> /eqP.
rewrite mulnC mulnSr - {3} (add0n (fusc n.+1)) eqn_add2r muln_eq0 fusc_eq0 //=.
rewrite - mul2n muln_eq0/= => /eqP kz; move:ea; rewrite kz mul1n => /eq_add_S.
move =>->;  rewrite - doubleS !fusc_even; apply: fusc_coprime.
Qed.


Section SternMax.

Fixpoint Fib_fusc_rec n := 
  if n is m.+1 then let (a,b):= Fib_fusc_rec m in (b.*2.+1, a + b) else (0,0).

Definition Fib_fusc_sym n := 3*2^(n.-2) - (Fib_fusc_rec n).1.

Notation FMc n :=  (Fib_fusc_rec n).1.
Notation FMd n :=  (Fib_fusc_rec n).2.
Notation FMe n :=  (Fib_fusc_sym n).

Lemma FM_cE n: FMc (n.+1) =  (FMd n).*2.+1.
Proof. by rewrite /= (surjective_pairing (Fib_fusc_rec n)). Qed.

Lemma FM_dE n: FMd (n.+1) = (FMc n) + (FMd n).
Proof. by rewrite /= (surjective_pairing (Fib_fusc_rec n)). Qed.

Lemma FM_recc:
 [/\ FMc 0 = 0, FMc 1 = 1 & forall n, FMc (n.+2) = FMc (n.+1) + (FMc n).*2 ].
Proof.
by split => // n; rewrite FM_cE FM_dE FM_cE addSn doubleD addnC.
Qed.

Lemma FM_recd:
 [/\ FMd 0 = 0, FMd 1 = 0 & forall n, FMd (n.+2) = FMd (n.+1) + (FMd n).*2.+1].
Proof. by split => // n;  rewrite FM_dE FM_cE addnC. Qed.

Lemma FM_recE1 n: FMc n = (FMd n)  + (odd n).
Proof.
elim: n => // n; rewrite FM_dE FM_cE /= => ->.
by rewrite (addnAC _ (odd n)) addnn - addnA addnC; case: odd.
Qed.

Lemma FM_recd2 n: FMd (n.+1) =  (FMd n).*2 + (odd n).
Proof. by rewrite - addnn - addnA - FM_recE1 addnC FM_dE. Qed.

Lemma FM_recc2 n: FMc (n.+1) =  (FMc n - (odd n)).*2.+1.
Proof. by rewrite (FM_recE1 n) addnK FM_cE. Qed.

Lemma FM_dodd n: odd (FMd (n.+1)) = odd n.
Proof. by rewrite FM_recd2 odd_add odd_double /= oddb. Qed.

Lemma FM_codd n: odd (FMc (n.+1)).
Proof. by rewrite FM_recE1 odd_add FM_dodd /=; case: odd. Qed.

Definition zero_one_rep n:=
  nat_of_list(iter n (fun l => ~~(head true l) :: l) [::true]).

Lemma FM_d_val n: FMd n.+2 = zero_one_rep n.
Proof.
elim: n => //n Hrec; rewrite FM_recd2 Hrec /= addnC.
rewrite {2} /zero_one_rep /= -/(zero_one_rep _). 
set h := head _ _;suff: h =  ~~ odd n by  move => <-; case: h.
by rewrite /h {Hrec h}; elim: n => // n /= ->.
Qed.


Lemma FM_cdbound n :  (FMd n) <=  FMc n <= (FMd n) .+1.
Proof. by rewrite FM_recE1 addnC; apply/andP;split; case:odd. Qed.

Lemma FM_dbound n :  2 ^ n <= FMd (n.+2) < 2^(n.+1).
Proof.
elim: n => // n /andP[].
rewrite - leq_double  -ltn_Sdouble - mul2n - (mul2n (2^ _)) - !expnS. 
move => ha hb; rewrite FM_recd2 addnC; apply /andP; split.
   by apply: (leq_trans ha); case:odd.
by apply: leq_trans hb; case: odd.
Qed.

Lemma FM_cbound n: 2 ^ n <= FMc (n.+2) <= 2^(n.+1).
Proof.
move: (FM_cdbound n.+2) => /andP [sa sb].
move /andP: (FM_dbound n) => [sc sd].
by rewrite (leq_trans sc sa) (leq_trans sb sd).
Qed.

Lemma FM_ecval n: FMc n.+2 + FMe n.+2 = 3 * 2 ^ n.
Proof.
case/andP: (FM_cbound n) => [le1 le2].
rewrite /Fib_fusc_sym succnK succnK mulSn -expnS -(addnBA (2 ^ n) le2).
by rewrite - addnCA (addnC (FMc n.+2)) (subnK le2). 
Qed.

Lemma FM_ebound n: 2 ^ n <= FMe (n.+2) <= 2^(n.+1).
Proof.
move:(FM_cbound n). 
rewrite -(leq_add2r (FMe n.+2)) -(leq_add2r  (FMe n.+2) (FMc n.+2)).
by rewrite FM_ecval mulSn leq_add2l -expnS addnC leq_add2l andbC.
Qed.

Lemma FM_rece2 n: FMe n.+3 =  (FMe n.+2 + (odd n.+2)).*2.-1.
Proof. 
have sa: odd n.+2 + FMd n.+2 <= 3 * 2 ^ n.
  by rewrite addnC -FM_recE1 -FM_ecval leq_addr.
rewrite /Fib_fusc_sym FM_recc2 !succnK expnS mulnCA subnS -mul2n -mulnBr mul2n.
rewrite (FM_recE1 n.+2) addnK subnDA subnK //- (leq_add2r (FMd n.+2)).
by rewrite subnK // (leq_trans _ sa) // leq_addl.
Qed.

 Lemma FM_rece n:  FMe (n.+4) = FMe (n.+3) + (FMe n.+2).*2.
Proof.
rewrite FM_rece2 FM_rece2 /=.
case: (odd n); rewrite /negb addn0 ?subn0 addn1.
   by rewrite doubleS doubleS ! succnK addSn addnn.
move: (FM_ebound n); case (FMe n.+2); first by rewrite leqn0 expn_eq0 /=.
by move => x _; rewrite !doubleS !succnK addSn !addnS addnn.
Qed.


Lemma FM_ltce n: (FMc (n.+4)).+1 < FMe (n.+4).
Proof.
rewrite ltn_neqAle; apply/andP; split.
    rewrite FM_rece2 FM_recc2; case (FMe n.+3 + odd n.+3) => // m.
    rewrite doubleS succnK; apply /negP => /eqP h.
    by move: (f_equal odd h); rewrite /odd -/odd !odd_double.
elim:n => // n HR; move: (HR).
have oe: odd (n.+4) = ~~ (odd (n.+3)) by [].
rewrite (FM_recc2 n.+4) (FM_rece2 n.+2) FM_recc2 FM_rece2 oe.
case: (odd _); rewrite /negb addn0 subn0 addn1 subn1 doubleS.
  rewrite (doubleS (FMe n.+3).*2) ! succnK !ltnS !ltn_double. 
  by rewrite - doubleS leq_double. 
case: (FMe n.+3) => // k. 
by rewrite doubleS !succnK ltnS ltnS => /ltnW h; rewrite ltn_double ltnS.
Qed.

Lemma FM_c_value n: FMc n = if odd n then  ((2^n).+1) %/3 else ((2^n).-1)%/3.
Proof.
elim: n => //n; rewrite FM_recc2 expnS pow2_mod3'=> -> /=; case (odd n).
  rewrite /negb mulnSr mulnSr mulnCA -addnA (addnS _ 3) subn1 succnK mul2n.
  rewrite -addn3 -mulnSr -mulnSr !mulKn //. 
rewrite /= subn0  mulnSr  mulnCA - addnS mul2n -mulnSr !mulKn //.
Qed.

Lemma FM_e_value n (a := 5*(2^n)): 
   FMe n.+2 = if odd n then  (a.-1) %/3 else (a.+1)%/3.
Proof.
rewrite /a/Fib_fusc_sym FM_c_value/= expnS expnS mulnA pow2_mod3'.
case: (odd n); rewrite /negb mulnSr mulnSr mulnA (mulnDl 5 4).
  set q := ((2 ^ n).-2 %/ 3); set u := _ %/3; have ->: u = (4 * q + 3).
     by rewrite /u  mulnSr mulnSr mulnCA - addnA -addnS  -(mulnDr 3 _ 3) mulKn.
  rewrite subnDr addnC  addnA addnK ! mulnSr.
  by rewrite mulnCA -addnA addnS addnS succnK -(mulnDr 3 _ 3) mulKn // addnC.
rewrite (addnS _ 3) succnK mulnCA - mulnSr mulKn// addnS - addn1.
rewrite  -[X in _ - X]  (addn1) subnDr addnC.
rewrite addnA addnK  mulnSr - addnS  mulnCA addnC -(mulnDr 3 _ 2) mulKn //.
Qed.


Lemma FM_fuscc_val n: fusc (FMc n) = fib n.
Proof. 
move: n; apply: is_fib => // n.
rewrite FM_cE FM_dE FM_cE FM_recE1 (addnC (FMd n)) - addnA addnn. 
by case: (odd n); rewrite !fusc_odd -?doubleS fusc_even // addnC.
Qed.

Lemma FM_fusce_val n: fusc (FMe n.+2) = fib n.+2.
Proof.
move: (FM_cbound n); rewrite expn2S => sa.
by rewrite - FM_fuscc_val - (fusc_palindrome sa (FM_ecval n)).
Qed.

Lemma fusc_bound1 n k: k <= 2 ^ n -> fusc k <= fib (n.+1). 
Proof.
pose p n:=  forall k, k <= 2 ^ n -> fusc k <= fib n.+1.
suff: forall n, p n /\ p (n.+1) by move => h;exact: (proj1 (h n)).
rewrite/p; clear k p n;elim; first by split;case => // [][] // [].
move => n [Ha Hb]; split => // k.
rewrite fibSS - (odd_double_half k) expn2S; case: (odd k); last first.
  rewrite leq_double fusc_even => /Hb hb; apply:(leq_trans hb); apply:leq_addr.
rewrite ltn_double fusc_odd => sa.
move: sa (Hb _ sa) (Hb _ (ltnW sa)).
rewrite -(odd_double_half k./2) expn2S; case: (odd k./2).
   by rewrite - doubleS leq_double fusc_even=> /Ha sa _ sb; apply: leq_add.
rewrite (addnC (fib _)) fusc_even ltn_double => /ltnW /Ha sa sb _. 
by apply: leq_add. 
Qed.

Lemma fusc_bound2 n k: k <= 2 ^ (n.+1) -> 
  (fusc k <= fib n.+2 ?= iff ((k == (FMe n.+2))  || (k == (FMc n.+2)))).
Proof.
move => h; split; [ by apply:fusc_bound1 | apply/idP/idP; last first ].
  by case/orP => /eqP ->; rewrite ? FM_fusce_val ?FM_fuscc_val eqxx.
pose P n := forall k,
  k <= 2^n -> fusc k = fib n.+1 -> (k = FMe n.+1) \/ (k = FMc n.+1).
move: n k h; suff: forall n, P n /\ P n.+1.
  move => H n k ha /eqP hb. 
  by case: (proj2 (H n) k ha hb) => ->; rewrite eqxx // orbT.
elim; first by split;case => //; case;(try by right); case => //; left.
move => n [Ha Hb];split; first by exact.
move => k;rewrite /P - (odd_double_half k); case: (odd k); last first.
  rewrite expn2S leq_double fusc_even => /fusc_bound1 => ha hb.
  by move: ha; rewrite hb leqNgt fib_smonotone // leqnn.
have sp q: q.*2.+1 = FMe n.+2 -> n <> 0.
  have: odd  (q.*2.+1) by rewrite /= odd_double. 
  by case n => // h1 h2; move: h1; rewrite h2.
rewrite expn2S  ltn_double fusc_odd  - (odd_double_half k./2).
set q := ((k./2)./2); case:(odd k./2).
  rewrite - doubleS fusc_even => sa.
  have sa': q.*2.+1 <= 2 ^ n.+1 by apply: ltnW; rewrite - doubleS.
  move:(sa); rewrite expn2S add1n leq_double => sb sc.
  move: (fib_sum_bound (fusc_bound1 sa') (fusc_bound1 sb) sc) => [ea eb].
  rewrite - addnn add1n - addnS - doubleS.
  move:(Ha _ sb eb) (Hb _ sa' ea).
   case => eqa; case => eqb; rewrite eqb eqa.
   + by move: (sp _ eqb);case n  => // n' _; left; rewrite FM_rece.
   + move: eqb eqa; rewrite FM_recc2 =>/eqP; rewrite eqSS eqn_double => /eqP->.
     case n => //; case; [by left | case; [ by right | move => m eq1]].
     by move:(FM_ltce m); rewrite - eq1 ltnS ltnNge leq_subr.
   + move: eqb  (sp _ eqb); rewrite - (succnK (q.*2.+1)) - doubleS eqa.
     case n => //; case; [ by right | case; [ by left |]].
     move => n1 /eqP; rewrite FM_rece2; move: (FM_ltce n1).
     case:(FMe n1.+4) => // m; rewrite  addSn doubleS  succnK.
     case:(FMc n1.+4) => // m';  rewrite doubleS  succnK eqSS eqn_double.
     by move => h /eqP h'; move:h; rewrite h' ltnS - addnS  ltnNge leq_addr.
   + by right; move:(FM_recc) => [ _ _ h]; rewrite - h.
rewrite add0n => sa. 
move: (sa); rewrite expn2S ltn_double addnC fusc_even => sb sc.
move:  (fib_sum_bound (fusc_bound1 sa) (fusc_bound1 (ltnW sb)) sc) => [ea eb].
rewrite - addnn  add1n - addSn. 
move:(Ha _ (ltnW sb) eb) (Hb _ sa ea).
case => eqa; case => eqb; rewrite eqb eqa.
+ by move: (sp _ eqb); case n => // n'; rewrite  FM_rece; left.
+ move: eqb eqa; rewrite FM_recc2 =>/eqP; rewrite eqSS eqn_double => /eqP->.
  case n => //; case; [by left | case; [ by right | move => m eq1]].
  by move:(ltnW(FM_ltce m)); rewrite - eq1 ltnNge leq_subr.
+ move: eqb  (sp _ eqb); rewrite eqa. 
  case n => //; case; [ by right | case; [ by left |]].
  move => n1 /eqP; rewrite FM_rece2; move: (FM_ltce n1).
  case:(FMe n1.+4) => // m. rewrite addSn doubleS succnK eqSS eqn_double ltnS.
  by move => h /eqP h'; move:h; rewrite h' ltnNge leq_addr.
+ by right; move:(FM_recc) => [ _ _ h]; rewrite - h.
Qed.

End SternMax.

(* Diagonals of the Pascal triangle *)
Lemma bin_mod2_rec1 n k :
  'C(n.+2, k.+2) = 'C(n, k.+2) + 'C(n, k)  %[mod 2].
Proof.
rewrite !binS addnA -(addnA 'C(n, k.+2)) (addnC 'C(n, k.+2)) addnn -muln2.
by rewrite - addnA modnMDl.
Qed.


Lemma bin_mod2_rec2 n k: 'C(n.*2,k.*2) = 'C(n, k)  %[mod 2].
Proof.
case:k; [ by  rewrite !bin0 | elim:n; first by move => k; rewrite !bin0n].
move => n Hrec k; rewrite doubleS doubleS bin_mod2_rec1 -doubleS.
rewrite - modnDm Hrec; case: k; first by rewrite bin0 !bin1 modnDm addn1.
by move => k; rewrite Hrec modnDm binS.
Qed.

Lemma bin_mod2_prop1 n k: 'C(n.*2,k.*2.+1) %%2 = 0.
Proof.
elim:n k =>[k | n Ihn [|k]]; first by rewrite bin0n.
   by rewrite bin1 -mul2n modnMr.
by rewrite !doubleS bin_mod2_rec1 -modnDm -doubleS Ihn Ihn. 
Qed.

Lemma bin_mod2_prop2 n k: 'C(n.*2.+1,k.*2) = 'C(n, k)  %[mod 2].
Proof.
case: k; first by rewrite !bin0.
move => k; rewrite doubleS binS -modnDm bin_mod2_prop1 - doubleS.  
by rewrite bin_mod2_rec2 addn0 modn_mod.
Qed.

Lemma bin_mod2_prop3 n k: 'C(n.*2.+1,k.*2.+1) = 'C(n, k)  %[mod 2].
Proof.
by rewrite binS -modnDm bin_mod2_prop1 bin_mod2_rec2 add0n modn_mod.
Qed.

Lemma binom_evenP n k:  ~~(odd 'C(n,k)) <->
   exists i, n %% (2 ^ i) < k %% (2^i).
Proof.
have ->: ~~(odd 'C(n,k)) = ('C(n, k) %% 2 == 0).
  move: (ltn_pmod 'C(n, k) (leqnSn 1)); rewrite {2} (divn_eq 'C(n, k) 2). 
  rewrite odd_add muln2 odd_double //=; case: ( _ %% 2) => // [] [] //.
move: n {-2} n (leqnn n)  k; elim.
  move => n;rewrite leqn0 => /eqP ->.
  case; first by split => // [] [i]; rewrite mod0n //.
  move => k; split => // _; exists k.+1; rewrite mod0n; rewrite modn_small //.
  by apply: ltn_expl. 
move => m Hrec n; rewrite leq_eqVlt ltnS;case/orP; last by apply:Hrec.
move /eqP  => -> k.
have ha: (m.+1)./2  <= m by apply: half_le2.
move:(Hrec _ ha k./2) => Hc.
rewrite - (odd_double_half m.+1) -(odd_double_half k). 
case:(odd m.+1); case(odd k).
+ rewrite bin_mod2_prop3; split.
    by move/Hc => [i]; exists i.+1; rewrite !rem_two_prop2 ltnS ltn_double.
  move => []; case; first by rewrite !modn1.
  by move => i; rewrite !rem_two_prop2 ltnS ltn_double => h; apply/Hc; exists i.
+ rewrite bin_mod2_prop2; split.
    move/Hc => [i ok]; exists (i.+1). 
    by rewrite rem_two_prop2 rem_two_prop1 -doubleS leq_double.
  move => []; case; first by rewrite !modn1.
  move => i; rewrite rem_two_prop2 rem_two_prop1 -doubleS leq_double.
  by move =>h; apply/Hc; exists i.
+ rewrite bin_mod2_prop1; split => // _; exists 1; rewrite expn1.
  by rewrite - !muln2 modnMl addnC modnMDl.
+ rewrite add0n bin_mod2_rec2; split.
    by move/Hc => [i ip]; exists i.+1; rewrite add0n !rem_two_prop1 ltn_double.
  move => [];case; first by rewrite ! modn1.
  by move => i; rewrite  !rem_two_prop1  ltn_double => h; apply/Hc; exists i.
Qed.


Lemma bin_mod2_sum_diag (f := fun n i => 'C(n.-1-i, i) %% 2) n:
  \sum_(i<n) (f n i) = fusc n.
Proof.
have Hu m: (m.*2.+1)./2 = m by exact:(half_bit_double m true). 
have Hv: forall n (i:'I_n),  n.-1.+1 = n /\ i.*2 <= (n.-1).*2.
  move => k i; move:(prednK (leq_ltn_trans (leq0n i)(ltn_ord i))) => eq.
  by split => //; rewrite leq_double - ltnS eq (ltn_ord i).
elim /fusc_ind: n.
+ by rewrite big_ord0.
+ by rewrite big_ord_recl big_ord0.
+ move => n H; rewrite fusc_even - H split_sum_even_odd1. 
  suff ->: \sum_(i < n) f n.*2 i.*2.+1 = 0.
    rewrite addn0 /f; apply: eq_bigr => i _; move:(Hv n i) => [eq1 lt1].
    by rewrite - {1} eq1 doubleS succnK subSn // - doubleB bin_mod2_prop2.
  apply: big1 => i _; rewrite /f;  move:(Hv n i) => [eq1 lt1].
  by rewrite - {1} eq1 doubleS succnK subSS- doubleB bin_mod2_prop1.
+ move => n Ha Hb; rewrite split_sum_even_odd fusc_odd Hu -Ha -Hb.
  rewrite -doubleS doubleK addnC /f; congr (_ + _);apply: eq_bigr => i _ /=.
    have [eq1 lt1] := (Hv n i).
    by rewrite -{1} eq1 doubleS subSn ?ltnS //subSS -doubleB bin_mod2_prop3.
  by rewrite -doubleB bin_mod2_rec2.
Qed.

Lemma sum_fusc_row n: \sum_(2^n <= i < 2^n.+1) (fusc i) = 3 ^n.
Proof.
transitivity (\sum_(i < 2^n) (fusc (i + 2^n))).
  by rewrite -{1}(add0n (2^n)) big_addn expn2S - addnn addnK big_mkord.
elim:n => //; first by rewrite expn0 big_ord_recr /= big_ord0.
move => n Hrec.
rewrite expn2S  (split_sum_even_odd1 (fun i =>fusc (i + (2 ^ n).*2))).
have ->: \sum_(i < 2 ^ n) fusc (i.*2 + (2 ^ n).*2) = 3^n.
  by rewrite - Hrec; apply: eq_bigr => i _; rewrite -doubleD fusc_even.
rewrite expnS mulSn - {3}Hrec mul2n - [in RHS] addnn; congr addn.
have {2} ->: \sum_(i < 2 ^ n) fusc (i + 2 ^ n) = 
   \sum_(i < 2 ^ n) fusc (i.+1 + 2 ^ n).
  have ep: 0 < 2 ^n by rewrite expn_gt0.
  rewrite -(prednK ep) big_ord_recl big_ord_recr /= addnC (prednK ep).
  rewrite add0n addnn fusc_even //.
rewrite - big_split /=; apply: eq_bigr => i _.
by rewrite addSn - doubleD fusc_odd addSn.
Qed.

Section FuscSum.

Local Open Scope ring_scope.

Lemma fuscq_eq0 n: ((fusc n)%:Q == 0) = (n == 0)%N.
Proof. by rewrite intq_eq0 - (fusc_eq0 n). Qed.

Lemma sum_Stern1 n:  \sum_(i<2^n) (Stern (i+2^n).*2) = (2^n)%N%:Q / 2%:Q.
Proof.
case: n; first by rewrite expn0  big_ord_recr /= big_ord0.
move => n. 
set p :=  (2^n)%N.
rewrite - (big_mkord xpredT (fun i => Stern (i + 2 ^ n.+1).*2)).
transitivity (p%:Q); last by rewrite expnS ratN_M mulrC mulKf //.
have ha: (0 <= 2^n)%N by [].
have hb: (2^n <= 2^n.+1)%N by rewrite leq_exp2l.
rewrite(big_cat_nat _ _ _ ha hb) /= [X in _ + X] big_nat_rev /=.
rewrite -/p -{2} (add0n p) big_addn expn2S -{2} addnn addnK -big_split /=.
rewrite big_mkord; transitivity (\sum_(i < p) 1 %:Q);
  last by rewrite sumr_const card_ord //.
rewrite -/p; apply: eq_bigr => i _.
have hc: (i + p < p.*2)%N by rewrite - addnn ltn_add2r (ltn_ord i).
set a := (i + p.*2)%N.
set c := (p + p.*2 - (i + p).+1 + p.*2)%N.
have he1: (a + c.+1 = 3 * (2^n.+1))%N.
  rewrite /a/c - (addnBA _ hc) - addSn (addnC i) - addnA - addSn (addnA i). 
  by rewrite (addnA i) addnS (subnKC hc) /p -expn2S addnn - mul2n -mulSn.
have he2: (a.+1 + c = 3 * (2^n.+1))%N. by rewrite addSnnS he1. 
have lt0: (a < (2^n.+1).*2)%N. 
   rewrite expn2S -/p  /a -(addnn p.*2) ltn_add2r - addnn ltn_addr //.
have hl1: ((2^n.+1) <= a <= (2^n.+1).*2)%N.
  by rewrite (ltnW lt0) expn2S -/p /a leq_addl //. 
have hl2: ((2^n.+1) <= a.+1 <= (2^n.+1).*2)%nat.
  rewrite lt0 expn2S -/p /a ltnW //  ltnS leq_addl //. 
rewrite /Stern ! fusc_even ! fusc_odd.
rewrite - (fusc_palindrome hl1 he1) - (fusc_palindrome hl2 he2) addnC.
by rewrite - mulrDl addrC -ratN_D divff // addnC - fusc_odd fuscq_eq0.
Qed.

Lemma sum_Stern n: \sum_(i<2^n) (Stern (i+2^n)) = ((3* 2^n)%N%:Q -1) / 2%:Q.
Proof.
elim:n. 
   rewrite  expn0  big_ord_recr /= big_ord0 add0r add0n /Stern /fusc //=.
   by rewrite muln1  divff // divff //.
move => n Hrec.
set p := (2^n)%N%:Q.
pose f i := Stern (i + (2 ^ n).*2).
have Hu m: \sum_(i < m.*2) f i = \sum_(i < m) f i.*2 + \sum_(i < m) f i.*2.+1.
  elim:m; first by rewrite !big_ord0.
  by move => m Hr; rewrite doubleS !big_ord_recr /= Hr addrACA addrA.
have Ha: \sum_(i < 2 ^ n) f i.*2  = p / 2%:Q.
  by rewrite - sum_Stern1; apply: eq_bigr => i _; rewrite doubleD.
have Hb: p = p * 2%:Q /  2%:Q by rewrite mulfK.
have Hc: p = \sum_(i < 2 ^ n) 1 by rewrite sumr_const card_ord.
have Hd: \sum_(i<2^n) f i.*2.+1  = p + (3%:Q * p -1)/2%:Q.
  rewrite /f -ratN_M - Hrec Hc - big_split /=; apply eq_bigr => i _.
  rewrite addSn -doubleD /Stern -doubleS fusc_even fusc_odd ratN_D addf_div1 //.
  by rewrite fuscq_eq0.
rewrite expn2S Hu Hd Ha {2}Hb -mulrDl -mulrDl addrA addrA - ratN_M - ratN_M. 
by rewrite - ratN_D - ratN_D -mulnS mulnC addnn doubleMr.
Qed.



Lemma sum_Stern_simp n:
  \sum_(2^n<=i< 2^n.+1) 1/((fusc i) * (fusc i.+1))%N%:Q = 1%:Q.
Proof.
rewrite expn2S -addnn.
pose f k :=  \sum_(2 ^ n <= i < 2 ^ n + k) 1 / (fusc i * fusc i.+1)%N%:Q. 
suff: forall i, (i <= 2^n)%N -> f i = (fusc i)%:Q / (fusc (2^n +i)%N) %:Q.
  by move => H; rewrite -/(f _) H // addnn - expn2S ! fusc_pow2.
move => i;rewrite/f - {2} (add0n (2 ^ n)%nat) big_addn addKn big_mkord.
elim:i; first by rewrite big_ord0 mul0r.
move => i Hrec lim.
have hu: (fusc (2 ^ n + i))%:Q != 0.
   by rewrite fuscq_eq0 addn_eq0 expn_eq0.
have hv:(fusc (2 ^ n + i.+1))%:Q != 0.
 by rewrite addnS fuscq_eq0.
rewrite big_ord_recr /= (Hrec (ltnW lim)) -addSn (addnC i) (addnC i.+1).
rewrite div1r ratN_M invrM ?unitfE // - mulrDl addf_inv // -ratN_M mulnC.
rewrite -{2}[1]/(1%nat%:Q) - ratN_D addnC -(fusc_bezout2 lim).
by rewrite mulrAC mulnC ratN_M mulfK.
Qed.



End FuscSum.


Definition Fusci n a b := a * (fusc n) + b * (fusc n.+1).  

Lemma fusci_0 a b: Fusci 0 a b = b.
Proof. by rewrite /Fusci muln0 muln1 //. Qed.

Lemma fusci_even n a b: Fusci (n.*2) a b = Fusci n (a + b) b.
Proof. by rewrite /Fusci fusc_even fusc_odd mulnDr addnA - mulnDl.  Qed.

Lemma fusci_odd n a b: Fusci (n.*2.+1) a b = Fusci n a (a + b).
Proof. 
by rewrite /Fusci - doubleS fusc_even fusc_odd mulnDr - addnA -mulnDl.
Qed.

Lemma fusci_val n:Fusci n 1 0 = fusc n.
Proof. by rewrite /Fusci /= addn0 mul1n.  Qed.

Lemma fusci_vald n: Fusci n 1 1 = fusc n.*2.+1.
Proof.  by rewrite /Fusci fusc_odd !mul1n. Qed.

Lemma fusci_1 a b: Fusci 1 a b = a + b.
Proof. by move: (fusci_odd 0 a b); rewrite fusci_0. Qed.

Lemma fusci_palindrome_aux u u' v a b: 
   (u + u').+1 = 2^v ->
   Fusci (2 ^v + u) a b = Fusci (2^v + u') b a.
Proof.
elim: v u u' a b.
  move => u u' a b /eqP; rewrite eqSS addn_eq0; case/andP => /eqP -> /eqP ->.
  by rewrite ! fusci_1 addnC.
move => n Hrec u u' a b;rewrite expn2S => sa.
wlog: a b u u' sa / ~~(odd u) && odd u'.
  move => H; move: (odd_double (2 ^ n)); rewrite - {1} sa /odd -/odd odd_add.
  case od: (odd u) => /= ou. 
    by symmetry; apply: H => //; [ by rewrite addnC | move:ou; case (odd _)].
  by apply:H => //; rewrite od /=; move:ou; case (odd _).
move => /andP [h1 h2].
move: (odd_double_half u) (odd_double_half u'). 
rewrite (negbTE h1)  h2 add0n add1n => e1 e2.
move /eqP: sa; rewrite -e1 -e2 -addnS -doubleS -doubleD -doubleD eqn_double.
rewrite ! addnS -doubleD fusci_even fusci_odd (addnC a) => /eqP eq1.
by apply: Hrec.
Qed.

Lemma fusc_palindrome_bis u u' v w w'  
   (aux := fun u v w => (2 ^v + u).*2.+1 *(2 ^w)):
   (u + u').+1 = 2 ^ v -> 
   fusc (aux u v w)  = fusc (aux u' v w').
Proof.
suff : forall w u v, fusc (aux u v w) = Fusci (2^v + u) 1 1.
  by move => H; rewrite H H => /fusci_palindrome_aux.
rewrite /aux;elim {u u' v w w'}; first by move => u v;rewrite muln1 fusci_vald.
by move => n Hrec u v; rewrite expnSr mulnA muln2 fusc_even Hrec.
Qed.

Fixpoint bin_invert_aux L :=
  match L with 
   | true :: L' => true :: [seq ~~ i | i <- L']
   | false :: L' => false ::  bin_invert_aux L'
   | nil => nil
end.

Definition bin_invert n :=
   nat_of_bin (num_of_list (bin_invert_aux (list_of_num (bin_of_nat n)))).

Lemma bin_invert_19:  (bin_invert 19) = 29.
Proof. by []. Qed.

Lemma bin_invert_0:  (bin_invert 0) = 0.
Proof. by []. Qed.

Lemma bin_invert_1:  (bin_invert 1) = 1.
Proof. by []. Qed.


Lemma log2_bin_invert n: log2(bin_invert n) = log2 n.
Proof.
rewrite /bin_invert /log2 nat_of_binK num_of_list_sizeK.
case: (list_of_num (bin_of_nat n)) => // a l; elim: l a; first by case.
by move => a l H; case; [ rewrite /= size_map |  move: (H a); move => /= ->].
Qed.

Lemma bin_invert_odd n: odd n -> odd(bin_invert n).
Proof.
move => on; rewrite (oddE on).
case:  (n./2) => // m;rewrite /bin_invert bin_of_nato /=; case: (map _ _) => //.
by move => a l /=; rewrite natTrecE odd_double.
Qed.

Lemma bin_invert_double n: (bin_invert n.*2) = (bin_invert n).*2.
Proof.
case:n => // n; rewrite /bin_invert. 
set x := (list_of_num (bin_of_nat n.+1)).
have ->:(list_of_num (bin_of_nat (n.+1).*2)) = false::x by rewrite bin_of_nate.
rewrite {1}/bin_invert_aux -/bin_invert_aux {1}/num_of_list. 
have: exists a b, bin_invert_aux x = a :: b.
  move: (nat_list_succ n); rewrite -/x; case x => // b l _ /=; case:b.
    by exists  true, [seq ~~ i | i <- l].
 by exists false, (bin_invert_aux l).
by move => [a [b ->]];  rewrite /= natTrecE.
Qed.

Lemma bin_invert_exp2n n: bin_invert (2^n) =  2^n.
Proof. by elim: n => //n Hrec; rewrite expn2S bin_invert_double Hrec. Qed.

Lemma bin_invert_p1 n: 2^((log2 n).-1) < n -> 
  n + (bin_invert n) = 3* 2^ ((log2 n).-1).
Proof.
case: n => // n; case: (elogn2P n) => k q ->. 
case: q; [ by rewrite muln1 log2_pow // succnK // ltnn | move => q _].
elim: {n} k q; last first.
  move => n Hrec q. 
  rewrite expnS - mulnA mul2n bin_invert_double - doubleD Hrec // doubleMr.
  set x := 2^n *_; have: 0 < x by rewrite lt0n muln_eq0 expn_eq0.
  by move/prednK => <-; rewrite log2_double -expn2S -log2S_k succnK.
move => q.
rewrite mul1n /bin_invert /log2 - {1} (bin_of_natK ((q.+1).*2.+1)).
rewrite - {1} (list_of_numK (bin_of_nat (q.+1).*2.+1)).
set l := list_of_num _; have [u [s ->]]: exists u s,  l = true::u::s.
  rewrite /l bin_of_nato /list_of_num /list_of_pos -/list_of_pos.
  case(pos_of_nat' q) => [ p | p |].
  + by exists true,(list_of_pos p).
  + by exists false,(list_of_pos p).
  + by exists true, nil.
rewrite /bin_invert_aux map_cons /size -/size succnK expnS.
rewrite /num_of_list /pos_of_list -/(pos_of_list (u::s)) -/(pos_of_list (_::_)).
rewrite /nat_of_bin /nat_of_pos -/nat_of_pos !natTrecE addSn addnS - doubleD.
rewrite -doubleS mulnCA mul2n; apply/eqP; rewrite eqn_double; apply /eqP.
elim: s u => // a s Hrec. rewrite /size -/size expnS mulnCA mul2n.
by case;rewrite /= !natTrecE ?addSn ?addnS - doubleD - doubleS Hrec.
Qed.

Lemma bin_invertI n: bin_invert (bin_invert n) = n.
Proof.
case: n => //n; move:(log2_bnd n); rewrite /= leq_eqVlt => /andP[/orP].
case; first by move/eqP => <- _; rewrite !bin_invert_exp2n.
move => sa sb; move:(bin_invert_p1 sa) => sc.
have li := (log2_bin_invert n.+1).
set p :=  2 ^ (log2 n.+1).-1.
have sd:  p.*2 =  2 ^ log2 n.+1 by rewrite -expn2S - log2S_k.
have ha: p <= n.+1 <= p.*2 by rewrite (ltnW sa) sd (ltnW sb).
have:p <= bin_invert n.+1 <= p.*2.
  rewrite - (leq_add2l n.+1) - (leq_add2l n.+1  (bin_invert n.+1)). 
  by rewrite sc mulSn mul2n leq_add2r addnC leq_add2l andbC.
move /andP => [];rewrite leq_eqVlt => /orP; case.  
  move/eqP => se _; move/eqP: sc; rewrite -se -/p mulSnr eqn_add2r => /eqP sf.
  by move: sb; rewrite log2S_k expnS -sf ltnn.
rewrite /p -li => /bin_invert_p1; rewrite li - sc addnC => /eqP.
by rewrite eqn_add2r => /eqP.
Qed.


Lemma fusc_bin_invert n:fusc (bin_invert n) = fusc n.
Proof.
case: n => //n; move:(log2_bnd n); rewrite /= leq_eqVlt => /andP[/orP].
case; first by move /eqP => -{3 4} <- _; rewrite bin_invert_exp2n.
move => sa sb; move:(bin_invert_p1 sa); set u := bin_invert _ => sc.
symmetry;apply:(fusc_palindrome (i:= (log2 n.+1).-1)) => //.
by rewrite (ltnW sa) -expn2S - log2S_k (ltnW sb).
Qed.

Definition FusciL l a b := Fusci (nat_of_list l) a b.

Lemma fusciL_0 a b: FusciL nil a b = b.
Proof. by rewrite /FusciL/= fusci_0. Qed.

Lemma fusciL_even l a b: FusciL (false::l) a b = FusciL l (a + b) b.
Proof. by rewrite /FusciL /= fusci_even. Qed.

Lemma fusciL_odd l a b: FusciL (true::l) a b = FusciL l a (a + b).
Proof. by rewrite /FusciL /= fusci_odd. Qed.

Lemma fusciL_val l: 
   FusciL (rcons l true) 1 0 = fusc (nat_of_list (rcons l true)).
Proof.  by rewrite  /FusciL fusci_val. Qed.

Lemma fusciL_valn n: FusciL (list_of_num (bin_of_nat n)) 1 0 = fusc n.
Proof. 
case: n => // n.
move:(nat_list_succ' n); set q := list_of_num (bin_of_nat n.+1) => /eqP eq.
by rewrite eq fusciL_val nat_of_list_rT - eq /q list_of_numK bin_of_natK.
Qed.


Definition bin_invert_alt L:=
  let l := bin_invert_aux L in 
  if l is a :: l' then rcons (belast a l') true else l.


Lemma bin_invert_altE l a s: bin_invert_aux l = rcons s a ->  
   bin_invert_alt l = rcons s true.
Proof.
rewrite /bin_invert_alt => ->. 
by case:s => // b s; rewrite rcons_cons // belast_rcons.
Qed.



Lemma bin_invert_alt_compat n:
  bin_invert n =
  nat_of_bin (num_of_list (bin_invert_alt (list_of_num (bin_of_nat n)))).
Proof.
rewrite /bin_invert /bin_invert_alt.
case: (bin_invert_aux _) => // a l.
by rewrite lastI; case: (last a l) => //; rewrite num_of_list_false.
Qed.



Lemma bin_invert_correctA n l:
  bin_invert_alt (ncons n false (true:: (rcons l true))) =
   (ncons n false (true:: (rcons [seq ~~ i | i <- l] true))).
Proof.
rewrite -!cat_nseq -[in RHS] rcons_cons - rcons_cat.
apply:(bin_invert_altE (a:=false)).  
rewrite rcons_cat rcons_cons -{3}[false]/(~~ true) - map_rcons.
by elim:n => //n /= ->. 
Qed.

Lemma bin_invert_correctB n (L:= ncons n false [::true]):
  bin_invert_alt  L = L.
Proof.
rewrite /L - !cat_nseq cats1 /ncons; apply:(bin_invert_altE (a:=true)).  
by elim:{L} n => // n /= ->.
Qed.

Lemma aux_for_bin_invert n (L := list_of_num (bin_of_nat n.+1)):
  (exists k, L = ncons k false [::true]) \/ 
  (exists k l, L= ncons k false (true:: (rcons l true))).
Proof.
move: (nat_list_succ n); rewrite -/L => ha;rewrite - (revK L) ha. 
have A k: (rev (nseq k false)) = (nseq k false).
  have {2}->: k = (size (rev (nseq k false))) by rewrite size_rev size_nseq.
  by apply/all_pred1P;rewrite all_rev; apply/all_pred1P; rewrite size_nseq.
suff: (exists k, (behead (rev L)) = nseq k false) \/
   (exists k l,  (behead (rev L)) = rcons l true ++ nseq k false).
  case => [ [k H] | [k [l H]]] ; [left | right].
    by exists k; rewrite rev_cons H -cat_nseq cats1 A.
    exists k, (rev l). 
  by rewrite rev_cons H rev_cat A -cat_nseq rcons_cat rev_rcons.
elim: (behead _); first by left; exists 0.
clear => a l [ [k ->] | [k [s ->]]].
   by case: a; [ right; exists k, nil |left; exists k.+1 ].
by right;exists k, (a::s); rewrite rcons_cons.
Qed.

Lemma fusc_bin_inverse_dijkstra n: fusc (bin_invert n.+1) = (fusc n.+1).
Proof.
rewrite -(fusciL_valn n.+1) -fusciL_valn bin_invert_alt_compat nat_of_binK.
move: (aux_for_bin_invert n) => /=; set L := list_of_pos _; case.
  by move => [k ->]; rewrite bin_invert_correctB - cat_nseq cats1 num_of_listK.
move => [k [l ->]]. 
rewrite bin_invert_correctA -cat_nseq -rcons_cons -rcons_cat num_of_listK.
elim:k; last by move => k H; rewrite /= !fusciL_even H.
rewrite /=!fusciL_odd! addn0; elim: l (1){1 4}(1).
  by move => a b; rewrite !fusciL_odd !fusciL_0 addnC.
by move => x l H a b; case x; rewrite /= fusciL_even fusciL_odd H // addnC.
Qed.


Definition Fuscj n m := Fusci n (fusc m.+1) (fusc m).

Lemma fuscj_0 m:  Fuscj 0 m = fusc m.
Proof. by rewrite /Fuscj fusci_0. Qed.

Lemma fuscj_val n: Fuscj n 0 = fusc n.
Proof. by rewrite /Fuscj/Fusci mul0n mul1n //. Qed.

Lemma fuscj_even n m: Fuscj (n.*2) m = Fuscj n (m.*2).
Proof. by rewrite /Fuscj fusci_even fusc_even fusc_odd addnC. Qed.

Lemma fuscj_odd n m: Fuscj (n.*2.+1) m = Fuscj n (m.*2.+1).
Proof. by rewrite /Fuscj fusci_odd - doubleS fusc_even fusc_odd addnC. Qed.

Lemma fuscj_1 n: Fuscj 1 n = Fuscj 0 (n.*2.+1).
Proof. apply:(fuscj_odd 0). Qed.


Lemma fuscj_reverse n: Fuscj n 0 = Fuscj 0 (base2rev n).
Proof.
pose R a b := (b * 2^(log2 a) + (base2rev a)).
suff: forall a b, Fuscj a b = Fuscj 0 (R a b) by move => H; rewrite (H n 0).
have aux b: Fuscj 0 b = Fuscj 0 (R 0 b) by rewrite /R addn0 muln1.
elim/fusc_ind.
+  by move => b; apply: aux.
+  by move => b; rewrite /R muln2 addn1 fuscj_1.
+  case => // k Ha b.
   by rewrite /R base2rev_even fuscj_even log2_double expnS mulnA muln2 Ha.
+ move => k Ha _ b.
  rewrite /R base2r_odd log2_Sdouble expnS mulnA muln2 addnA - mulSnr.
  by rewrite fuscj_odd Ha. 
Qed.

Lemma fusc_reverse n:fusc (base2rev n) = fusc n.
Proof. by move: (fuscj_reverse n); rewrite fuscj_0 fuscj_val. Qed.

Lemma base2_rev_invert n: odd n -> n != 1 ->
  (base2rev n.-1) + bin_invert(base2rev n) = 2^(log2 n). 
Proof.
move => on nn1; have eq1:= (oddE on).
have pv: 2 ^ (log2 n).-1 = 2 ^ log2 n./2 by rewrite {1} eq1 log2_Sdouble succnK.
move: (base2r_odd n./2); rewrite - eq1 - pv => eq2.
case H: (base2rev n./2 == 0).
   move: eq2 nn1; rewrite {1 4} eq1 (eqP H) addn0 => sa.
   move:(odd_base2rev (n./2).*2); rewrite sa pv; case (n./2) => // q.
   by rewrite log2S_k expn2S odd_double.
rewrite {1 3} eq1 log2S_k succnK  base2rev_even  -eq1 expnS.
have: 2 ^ (log2 n).-1 < base2rev n.  
  by rewrite eq2 - (@prednK (base2rev n./2)) ?lt0n ?H // addnS ltnS leq_addr.
rewrite -(log_base2r on) => leq1; apply /eqP.
rewrite -(eqn_add2l (base2rev n)) addnCA (bin_invert_p1 leq1).  
by rewrite (log_base2r on) mulSn addnA eqn_add2r addnC - eq2.
Qed.

Lemma fusc_fusc2 a b: coprime a b -> 
   exists n m p, [/\ n + m = 2^p, a = fusc n & b = fusc m].
Proof.
wlog: a b/ a <= b.
  move => H; move: (leq_total a b); case /orP; first by apply: H.
  move => ba; rewrite coprime_sym => q; move:(H _ _ ba q).
  by move => [n [m [p [ea -> ->]]]]; exists m, n, p; rewrite addnC.
case: a; first by rewrite /coprime gcd0n => _ /eqP -> ;exists 0,1,0.
move => a; case: b; first by rewrite /coprime gcdn0 => _ /eqP ->;exists 1,0,0.
move => b h cp; move: h ;move:(fusc_pair_surj cp) => [k [ -> ->]].
case ok: (odd k). 
  by rewrite leqNgt; case: (fusc_monotone ok) => -> //; exists 1,1,1.
case kz: (k ==0); first by rewrite (eqP kz); exists 0,1,0.
exists (base2rev k.+1.-1), (bin_invert (base2rev k.+1)),(log2 k.+1); split.
+ by apply:base2_rev_invert => /=; rewrite ?ok //eqSS kz.
+ by rewrite succnK fusc_reverse.
+ by rewrite fusc_bin_invert fusc_reverse.
Qed.


Lemma fusc_fusc3 n m p: n + m = 2^p -> coprime (fusc n) (fusc m).
Proof.
wlog: n m/ n <= m.
  move => H; move: (leq_total n m); case /orP; first by apply: H.
  move => ba; rewrite coprime_sym addnC => q; exact:(H _ _ ba q).
case: p.
  move => _ /eqP;case: n; first by rewrite add0n;move/eqP => ->.
  by move => n; rewrite addSn eqSS addn_eq0 => /andP [/eqP -> /eqP ->].
move => p;case: m; first by rewrite addn0 => _ ->; rewrite fusc_pow2.
move => m; case: (elogn2P m) => k q -> leq2 eq2.
move:(leq_addl n (2 ^ k * q.*2.+1)); rewrite eq2 => l1.
have pp:0 < 2^k by rewrite expn_gt0.
have: 0 < q.*2.+1 by rewrite ltnS. 
rewrite -(leq_pmul2l pp) muln1 => eq3. 
move: (leq_trans eq3 l1); rewrite leq_exp2l // => lekp.
move: eq2; rewrite -{1}(subnK lekp)  (addnC _ k) expnD => eq2.
move:(addnK (2 ^ k * q.*2.+1) n); rewrite eq2 - mulnBr => eq4.
rewrite - eq4  ! fusc_kpow2n;set w := (2 ^ (p.+1 - k) - q.*2.+1).
have: w <= q.*2.+1 by rewrite  -(leq_pmul2l pp) eq4.
move/eqP: eq2; rewrite -eq4 -mulnDr eqn_mul2l expn_eq0 -/w /=;case: (p.+1 - k).
  rewrite addnS eqSS addn_eq0 => /andP [/eqP -> /eqP -> //].
move:(w);clear; move => w p eq1.
rewrite leq_eqVlt; case/orP => le1.
  move: eq1;rewrite (eqP le1) addnn expn2S eqn_double => /eqP ->.
  by rewrite fusc_pow2. 
have ok: odd (q.*2.+1) by rewrite /= odd_double.
have /andP[ le3 le4]: w <2^p <= q.*2.+1.
  rewrite -(leq_add2l w (2^p) q.*2.+1); move: (ltn_add2l w w q.*2.+1).
  rewrite (eqP eq1) le1 expn2S addnn ltn_double - addnn leq_add2r=> h.
  by rewrite h /= (ltnW h).
have ln: log2 (q.*2.+1) = p.+1.
  apply: log2_pr;rewrite le4 /=; case:(posnP w) => wp.
    by move: ok;rewrite - (add0n q.*2.+1) - wp (eqP eq1) expn2S odd_double.
  by rewrite -(eqP eq1)  - (prednK wp) addSn ltnS leq_addl.
have oiq:= (bin_invert_odd ok).
set n := base2rev(bin_invert (q.*2.+1)).
have eq3: bin_invert (base2rev n) = q.*2.+1.
  by rewrite /n (base2rev_oddI oiq) bin_invertI.
case: (posnP (bin_invert q.*2.+1)) => sa; first by move: oiq; rewrite sa /=.
case: (posnP n) => nz; first by move:eq3; rewrite nz //.
have on : odd n by rewrite /n - (prednK sa); apply: odd_base2rev.
rewrite - eq3 fusc_bin_invert fusc_reverse.
case en1:(n==1); first by rewrite (eqP en1) /coprime fusc1 /= gcdn1.
move: (log_base2r oiq) eq1; rewrite log2_bin_invert -/n ln => <-. 
rewrite - eq3 - (base2_rev_invert on (negbT en1)) eqn_add2r => /eqP ->.
rewrite fusc_reverse -{2}(prednK nz);apply:fusc_coprime.
Qed.

Lemma fusc_compare1 i j k: i < j -> i + j = 2 ^ k -> fusc i < fusc j.
Proof.
elim : k i j.
   rewrite expn0; case; first by move => j _; rewrite add0n => ->.
   move => i j lij /eqP; rewrite addSn eqSS addn_eq0 => /andP[ha hb].
   move: lij; rewrite (eqP ha) (eqP hb) //.
move => n H i j lij sij.
have oij: (odd (i + j)) == false by rewrite sij expn2S odd_double.
case: (odd_dichot i) => iv; case:(odd_dichot j) => jv.
+ move /eqP: sij.
  rewrite iv jv addnS addSn -doubleD -doubleS expn2S eqn_double -addnS => /eqP.
  move => ha; move:(ha); rewrite -addSnnS => hb.
  have hc: i./2 < j./2.+1 by rewrite ltnS -leq_double -ltnS -iv -jv; apply:ltnW.
  case xx: (i./2.+1 == j./2).
     by rewrite !fusc_odd (eqP xx) addnC ltn_add2l H.
  have hd: i./2.+1 < j./2 by rewrite ltn_neqAle xx -ltn_double -ltnS -iv -jv.
  by rewrite !fusc_odd addnC -addnS leq_add // ?(ltnW (H _ _ hd hb)) // H. 
+ by move: oij; rewrite iv jv odd_add /= !odd_double.
+ by move: oij; rewrite iv jv odd_add /= !odd_double.
+ rewrite iv jv !fusc_even; apply:H; first by rewrite - ltn_double - iv -jv.
  by apply/eqP; rewrite - eqn_double doubleD - iv - jv sij expn2S.
Qed.


Section Dijkstra.

Variable s: nat -> nat.


Definition Dijkstra_prop1:= forall n m p,
  n + m = 2^p -> coprime (s n) (s m).

Definition Dijkstra_prop2 := forall a b,
  coprime a b ->  exists n m p, [/\ n + m = 2^p, a = s n & b = s m].

Definition Dijkstra_prop1bis :=
  forall n,  coprime (s n) (s n.+1).

Definition Dijkstra_prop2bis := forall a b,
  coprime a b.+1 -> exists k, a = s k /\ b.+1 = s k.+1.

Hypothesis DH_FR: forall n, s (base2rev n) = s n.
Hypothesis DH_BI: forall n, s (bin_invert n) = s n.
Hypothesis DH_1: s 1 = 1.

Lemma DH_power_two k n: s (2 ^ n * k) = s k.
Proof.
rewrite - DH_FR - (DH_FR k); congr s; elim:n => //.
  by rewrite mul1n.
by move => n <-; rewrite expnS - mulnA mul2n base2rev_even.
Qed.


Lemma DH_palindrome i a b:
  let p := 2 ^ i in  p <= a <= p.*2 ->  a + b = 3 * p -> s a = s b.
Proof.
move => /= /andP [le1 le2] eq1.
have H k: s k.*2 = s k by rewrite - DH_FR base2rev_even DH_FR.
move: le2; rewrite leq_eqVlt; case/orP => le2.
   move /eqP:eq1; rewrite (eqP le2)  (mulnDl 2 1) mul1n mul2n eqn_add2l.
   by move/eqP ->. 
have /log2_pr loga: 2 ^ i <= a <  2 ^ i.+1 by rewrite expnS mul2n le1 le2.
move: le1; rewrite leq_eqVlt; case/orP => le1.
  move /eqP:eq1; rewrite (eqP le1)  (mulnDl 1 2) mul1n mul2n eqn_add2l.
  by move/eqP ->.
have /bin_invert_p1: 2 ^ (log2 a).-1 < a by rewrite loga. 
by move/eqP; rewrite loga - eq1  eqn_add2l => /eqP <-.
Qed.

Lemma DH_palindrome_res k:  0 < k ->
 exists m, [/\ (k == 1) || odd (m+k), s k = s m.+1 & s k.+1 = s m].
Proof.
move => knz.
move: (prednK knz) => kv.
move: (log2_bnd k.-1); rewrite /= {2} log2S_k kv; set i := (log2 _).-1.
rewrite expnS mul2n;set p := 2 ^i; set m := 3 * p - k.+1.
move => /andP[le1 le2].
have ra:  k.+1 + m = 3 * p.
  rewrite /m addnC subnK //  (mulnDl 1 2 p) mul1n mul2n.
  by apply:(leq_trans le2); apply: leq_addl.
have rb: m.+1 +k = 3 * p by rewrite addnC - addSnnS.
have le3 : p <= k.+1 <= p.*2 by rewrite  le2 andbT ltnW.
have rc: p <= m.+1.
  by rewrite -(leq_add2r k) rb  (mulnDl 1 2 p) mul1n mul2n leq_add2l ltnW.
have rd: m.+1 <= p.*2.
  by rewrite -(leq_add2r k) rb  (mulnDl 2 1 p) mul1n mul2n leq_add2l.
have le4: p <= m.+1 <= p.*2 by rewrite rc rd.
have okm: (k == 1) || odd (m+k).
  move:(f_equal odd ra); rewrite addSn odd_mul /p odd_exp /= orbF.
  move:le2; rewrite  addnC /p; case: (odd (m+k)); first by rewrite orbT.
  case iz: (i==0) => //. rewrite (eqP iz) /=. move: knz. clear.
  by case: k => //;case.
exists m; split => //.
  by rewrite(DH_palindrome le4 rb).
exact:(DH_palindrome le3 ra).
Qed.


Lemma DH_prop1_to_bis: 
   Dijkstra_prop1 -> Dijkstra_prop1bis.
Proof.
move => hyp n.
wlog: n/ ~~(odd n).
  move => H; case on: (odd n); last by apply: H => //; rewrite on.
  case: (posnP n) => nz;first by rewrite nz DH_1 /coprime gcdn1.
  case n1: (n==1); first by rewrite (eqP n1) DH_1  coprime1n. 
  move:(DH_palindrome_res nz) => [m [mp -> ->]].
  rewrite /coprime gcdnC;apply: H.
  by move: mp; rewrite n1 odd_add on /= addbT.
case: n=> [ | n on ]; first by rewrite DH_1 coprimen1.
move: (base2_rev_invert (on: odd n.+2) (is_true_true: (n.+2 != 1))).
by move/hyp;rewrite DH_BI ! DH_FR.
Qed.


Lemma DH_prop2_from_bis: s 0 = 0 -> 
  Dijkstra_prop2bis ->  Dijkstra_prop2. 
Proof.
move => sv0 hyp a b.
pose prop2_aux a b := exists n m p, [/\ n + m = 2^p, a = s n & b = s m].
have sym u v: prop2_aux u v -> prop2_aux v u.
  by move => [n [m [k [ha hb hc]]]]; exists m, n, k; split => //; rewrite addnC.
case:b; first by rewrite /coprime gcdn0 => /eqP ->; exists 1,0,0. 
move => b /hyp [k [ -> ->]]. 
case: (posnP k) => kp; first by rewrite kp DH_1 sv0; exists 0,1,0.
case ek1: (k==1).
  by rewrite (eqP ek1) - (muln1 2) -[2]/(2^1) DH_power_two; exists 1,1,1.
suff: forall m, ~~(odd m) -> prop2_aux (s m) (s m.+1).
   move => H; case ok: (odd k); last by apply: H => //; rewrite ok.
   move:(DH_palindrome_res kp); move => [m [hm -> ->]].
  by apply: sym; apply: H; move: hm; rewrite odd_add ek1 ok addbT.
move => m om.
case mz: (m ==0); first by rewrite (eqP mz); exists 0,1,0.
exists (base2rev m.+1.-1), (bin_invert (base2rev m.+1)),(log2 m.+1); split.
+ by apply:base2_rev_invert => /=; rewrite ?om //eqSS mz.
+ by rewrite succnK DH_FR.
+ by rewrite DH_BI DH_FR.
Qed.

Lemma DH_prop1_from_bis: 
  Dijkstra_prop1bis ->  Dijkstra_prop1.
Proof.
move =>  hyp n m p.
have DP_H4_spec k: s (2 ^ k) = 1 by rewrite -(muln1 (2 ^k)) DH_power_two DH_1.
wlog: n m/ n <= m.
  move => H; move: (leq_total n m); case /orP; first by apply: H.
  move => ba; rewrite coprime_sym addnC => q; exact:(H _ _ ba q).
case:m; first by rewrite leqn0 => /eqP -> /esym /eqP; rewrite expn_eq0 //.
move => m; case: (elogn2P m) => k q -> leq2 eq2.
move:(leq_addl n (2 ^ k * q.*2.+1)); rewrite eq2 => l1.
have pp:0 < 2^k by rewrite expn_gt0.
have: 0 < q.*2.+1 by rewrite ltnS. 
rewrite -(leq_pmul2l pp) muln1 => eq3. 
move: (leq_trans eq3 l1); rewrite leq_exp2l // => lekp.
move: eq2; rewrite -{1}(subnK lekp)  (addnC _ k) expnD => eq2.
move:(addnK (2 ^ k * q.*2.+1) n); rewrite eq2 - mulnBr => eq4.
rewrite - eq4 ! DH_power_two ;set w := (2 ^ (p - k) - q.*2.+1).
have: w <= q.*2.+1 by rewrite  -(leq_pmul2l pp) eq4.
move/eqP: eq2; rewrite -eq4 -mulnDr eqn_mul2l expn_eq0 -/w /=;case: (p - k).
 by rewrite addnS eqSS addn_eq0 => /andP [/eqP -> /eqP -> ].
move:(w); clear n p m leq2 l1 lekp eq4 w eq3; move => w p eq1.
rewrite leq_eqVlt; case/orP => le1.
  move: eq1;rewrite (eqP le1) addnn expn2S eqn_double => /eqP ->.
  by rewrite DP_H4_spec. 
have ok: odd (q.*2.+1) by rewrite /= odd_double.
have /andP[ le3 le4]: w <2^p <= q.*2.+1.
  rewrite -(leq_add2l w (2^p) q.*2.+1); move: (ltn_add2l w w q.*2.+1).
  rewrite  (eqP eq1) le1 expn2S addnn ltn_double - addnn leq_add2r=> h.
  by rewrite h /= (ltnW h).
have ln: log2 (q.*2.+1) = p.+1.
  apply: log2_pr;rewrite le4 /=; case:(posnP w) => wp. 
    by move: ok;rewrite - (add0n q.*2.+1) - wp (eqP eq1) expn2S odd_double.
  by rewrite -(eqP eq1)  - (prednK wp) addSn ltnS leq_addl.
have oiq:= (bin_invert_odd ok).
set n := base2rev(bin_invert (q.*2.+1)).
have eq3: bin_invert (base2rev n) = q.*2.+1.
  by rewrite /n (base2rev_oddI oiq) bin_invertI.
case: (posnP (bin_invert q.*2.+1)) => sa; first by move: oiq; rewrite sa /=.
case: (posnP n) => nz; first by move:eq3; rewrite nz //.
have on : odd n by rewrite /n - (prednK sa); apply: odd_base2rev.
rewrite - eq3 DH_BI DH_FR.
case en1:(n==1); first by rewrite (eqP en1) /coprime DH_1 /= gcdn1.
move: (log_base2r oiq) eq1; rewrite log2_bin_invert -/n ln => <-. 
rewrite - eq3 - (base2_rev_invert on (negbT en1)) eqn_add2r => /eqP ->.
by rewrite DH_FR -{2}(prednK nz) hyp.
Qed.

Lemma DH_prop2_to_bis: s 0 = 0 ->
  Dijkstra_prop2 -> Dijkstra_prop2bis.
Proof.
move=> sv0 hyp a b.
case eab:(a==b.+1).
  rewrite -(eqP eab) /coprime -{2} (mul1n a) gcdnMl => /eqP ->.
  by exists 1; rewrite (DH_power_two 1 1) DH_1.
move: eab; case: a.
  by rewrite /coprime gcd0n => _ /eqP ->; exists 0; rewrite sv0 DH_1.
move => a eab cp.
have: a.+1 != 0 by [].
have: b.+1 != 0 by [].
move /hyp: cp => [n [m [p []]]].
case:m => [ |m nmp av bv]; first  by rewrite sv0.
move: eab nmp; rewrite av bv.
case: (elogn2P m) => k q -> nsv nmp.
move:(leq_addl n (2 ^ k * q.*2.+1)); rewrite nmp => le1.
have pp:0 < 2^k by rewrite expn_gt0.
have: 0 < q.*2.+1 by rewrite ltnS. 
rewrite -(leq_pmul2l pp) muln1 => eq3.
move: (leq_trans eq3 le1); rewrite leq_exp2l // => lekp.
move: nmp; rewrite -{1}(subnK lekp)  (addnC _ k) expnD => nmp.
move:(addnK (2 ^ k * q.*2.+1) n); rewrite nmp - mulnBr => eq4.
move: nsv.
rewrite - eq4 ! DH_power_two; set w := _ - _.
have nmp': w + q.*2.+1 = 2 ^ (p - k).
  rewrite /w; apply: subnK.
  by rewrite -(leq_pmul2l pp) - nmp;  apply: leq_addl.
case: (posnP (p - k)) => ltkp.
  move /eqP:nmp'; rewrite ltkp /= addnS eqSS addn_eq0.
  by move => /andP [/eqP -> /eqP ->]; exists 0.
case: (odd_dichot w) => ow2; last first.
  have: (odd (2 ^ (p - k))) by rewrite  -nmp' odd_add ow2 /= !odd_double /=.
  by rewrite odd_exp /= orbF => /eqP e0; move: ltkp; rewrite e0.
move: nmp'; rewrite ow2 - (prednK ltkp).
move:(w./2) ((p-k).-1).
clear a b n m p k ltkp le1 pp eq3 lekp nmp eq4 w ow2 av bv.
move => q' p.
wlog: q q' / q' <= q.
  move => H eq1 neq1 anz bnz.
  case/orP:(leq_total q' q) => leqq; first by apply: H. 
  rewrite addnC in eq1; rewrite eq_sym in neq1.
  move:(H q' q leqq eq1 neq1 bnz anz) => [k [eqa eqb]].
  case: (posnP k) => kz; first by move: anz; rewrite eqa kz sv0.
  move:(DH_palindrome_res kz) => [m [_ ma mb]].
  by exists m; rewrite eqa eqb ma mb.  
move => le1 nmp nsv _ _ ; move: le1.
rewrite leq_eqVlt; case/orP => le1.
  by move/eqP: nsv; rewrite (eqP le1).
have le2:  q'.*2.+1 < q.*2.+1 by rewrite ltnS ltn_double.
have ok: odd (q.*2.+1) by rewrite /= odd_double.
set w :=  q'.*2.+1.
have /andP[ le3 le4]: w <2^p <= q.*2.+1.
  rewrite -(leq_add2l w (2^p) q.*2.+1); move: (ltn_add2l w w q.*2.+1).
  rewrite  nmp /w le2 expn2S addnn ltn_double - (addnn (2^p)) leq_add2r=> h.
  by rewrite h /= (ltnW h).
have ln: log2 (q.*2.+1) = p.+1.
  apply: log2_pr;rewrite le4 /=; case:(posnP w) => wp.
    by move: ok;rewrite - (add0n q.*2.+1) - wp nmp expn2S odd_double.
  by rewrite - nmp  -/w - (prednK wp) addSn ltnS leq_addl.
have oiq:= (bin_invert_odd ok).
set n := base2rev(bin_invert (q.*2.+1)).
have eq3: bin_invert (base2rev n) = q.*2.+1.
  by rewrite /n (base2rev_oddI oiq) bin_invertI.
case: (posnP (bin_invert q.*2.+1)) => sa; first by move: oiq; rewrite sa /=.
case: (posnP n) => nz; first by move:eq3; rewrite nz //.
have on : odd n by rewrite /n - (prednK sa); apply: odd_base2rev.
rewrite /w - eq3 DH_BI DH_FR.
case en1:(n==1).
  move: eq3; rewrite (eqP en1) /bin_invert/base2rev /= => eq4.
  by move: le2; rewrite - eq4 ltnS ltn0.
move: (log_base2r oiq) nmp; rewrite log2_bin_invert -/n ln => <-. 
move/eqP;rewrite - eq3 - (base2_rev_invert on (negbT en1)) eqn_add2r => /eqP ->.
by rewrite DH_FR -{2}(prednK nz); exists (n.-1).
Qed.

                                      
End Dijkstra.


(* -- *)


Section WeakBaseTwoRepresentation.

Fixpoint wbase2 (l: seq 'I_3) :=
  if l is a :: l' then a + (wbase2 l').*2 else 0.

Definition ord1_3:= (Ordinal (isT:1<3)).
Definition ord2_3:= (Ordinal (isT:2<3)).

Lemma Ord3_trichot (a: 'I_3): (a == ord0) (+) (a == ord1_3) (+) (a == ord2_3).
Proof.
case:a =>m H.
have ->: (Ordinal H == ord0) = (m==0).
  by apply/eqP/eqP => xx; [ move:(f_equal val xx)|  apply:val_inj ].
have ->: (Ordinal H == ord1_3) = (m==1).
  by apply/eqP/eqP => xx; [ move:(f_equal val xx)|  apply:val_inj ].
have ->: (Ordinal H == ord2_3) = (m==2).
  by apply/eqP/eqP => xx; [ move:(f_equal val xx)|  apply:val_inj ].
move: H; rewrite leq_eqVlt eqSS; case/orP; first by move => /eqP -> //.
by rewrite !ltnS leqn1; case/orP => /eqP ->.
Qed.

Lemma wbase2_rec_nat (a:nat) l (H: a < 3):
  wbase2 (Ordinal H :: l) = a + (wbase2 l).*2.
Proof. by []. Qed.

Lemma wbase2_recr a l: wbase2 (rcons l a) = wbase2 l + 2 ^ size l * a.
Proof.
elim: l a => [a | a l H b]; first by rewrite /= addn0 mul1n //.
by rewrite /= H doubleD addnA doubleMl expn2S.
Qed.

Lemma wbase2_cat l1 l2: 
  wbase2 (l1 ++ l2) =  wbase2 l1 + (2^(size l1)) * (wbase2 l2).
Proof.
elim: l2 l1; first by move => l1; by rewrite muln0 addn0 cats0.
move => a l2 H l1;rewrite - cat_rcons H size_rcons /= mulnDr addnA.
by rewrite -doubleMr doubleMl -expn2S wbase2_recr.
Qed.

Lemma wbase2_zero l : wbase2 l = 0 -> l = nseq (size l) ord0.
Proof. 
move => h; apply /all_pred1P.
elim:l h=> // a l Hr /= /eqP; rewrite addn_eq0 double_eq0=> /andP[/eqP ha /eqP].
by move/Hr => ->; rewrite andbT; apply/eqP; apply:val_inj.
Qed.

Lemma wbase2_pad l k: wbase2 (l ++ nseq k ord0) = wbase2 l.
Proof. 
suff: wbase2 (nseq k ord0) = 0 by move => h;rewrite wbase2_cat h muln0 addn0.
by elim:k => // n /= ->.
Qed.

Lemma wbase2_split l n: log2 n <= size l -> wbase2 l = n ->
  l = take (log2 n) l ++ nseq ((size l) - log2 n) ord0.
Proof.
move => sa sb.
move: (size_takel sa)(cat_take_drop (log2 n) l) => sc sd.
move: sb; rewrite -{1 2} sd wbase2_cat sc => ea.
have: n <  2 ^ log2 n by clear; case: n => // n; move/andP:(log2_bnd n) =>[].
rewrite - {1} ea; case: (posnP (wbase2 (drop (log2 n) l))) => res.
   by move => _; rewrite (wbase2_zero res) size_drop.
move => h.
by move: (leq_trans h (leq_pmulr ( 2 ^ log2 n) res));rewrite ltnNge leq_addl.
Qed.

Definition bool_to_I3 (a: bool) := if a then ord1_3 else ord0.

Lemma wbase2_correct n:
  wbase2 [seq bool_to_I3 i | i<- (list_of_num (bin_of_nat n))] = n.
Proof.
case: n => // n; rewrite - {2}(pos_of_natK n) /= /pos_of_nat'.
by elim: (pos_of_nat n n) => //= p ->; rewrite natTrecE //.
Qed.

Lemma wbase2_odd l : odd (wbase2 l) <-> head ord0 l = ord1_3.
Proof.
case: l => // a l /=. 
rewrite odd_add odd_double addbF; split; last by move => ->.
move: (Ord3_trichot a); case: eqP; first by move => ->.
by case: eqP => // _ _ /= /eqP ->.
Qed.

Lemma wbase2_odd1 n l : 
  wbase2 l = n.*2.+1 -> head ord0 l = ord1_3 /\ wbase2 (behead l) = n.
Proof.
move => h. 
have /wbase2_odd h': (odd (wbase2 l)) by rewrite h /= odd_double.
by move: h' h; case: l => // a l /= -> /eqP; rewrite eqSS eqn_double => /eqP. 
Qed.

Lemma wbase2_double_nz n l (a := head ord0 l) (l' := behead l):
  wbase2 l = n.*2.+2 -> l = a :: l' /\
   ((a == ord0) && (wbase2 l' == n.+1) (+) ((a == ord2_3) && (wbase2 l' == n))).
Proof.
move => ea.
move:(Ord3_trichot a).
case eb: (a == ord1_3). 
  by move/eqP:eb => /wbase2_odd;  rewrite ea /= odd_double.
move /eqP: ea;rewrite addbF.  rewrite /a/l'; clear;case: l => // a l /= ea.
case: eqP => az.
  by move: ea;rewrite az /= -doubleS eqn_double => ->.
by move=> /= eb; move: ea; rewrite eb {1} (eqP eb) add2n !eqSS eqn_double => ->.
Qed.

Lemma tcast_val (T: Type) m n (H: m = n) (l: m.-tuple T): 
  tval (tcast H l) = tval l.
Proof. by case: n / H. Qed.


Definition tuple_padl n k (l: n.-tuple 'I_3) := 
   (l ++ (nseq (k - n) ord0)).

Fact size_tuple_padl  n k (l: n.-tuple 'I_3): n <= k  
  -> size (tuple_padl k l) = k.
Proof. 
by move/subnKC => eq1; rewrite /tuple_padl size_cat size_nseq size_tuple /=. 
Qed.

Definition tuple_pad k n (l:n.-tuple 'I_3) (H: n <= k) :=
  (tcast (size_tuple_padl l H) (in_tuple (tuple_padl k l))).

Lemma tuple_pad_val k n (l:n.-tuple 'I_3) (H: n <= k):
  tval (tuple_pad l H) = tval l ++  (nseq (k - n) ord0).
Proof. by rewrite /tuple_pad  /tuple_padl  tcast_val. Qed.

Lemma wbase2_tuple_pad k n (l:n.-tuple 'I_3) (H: n <= k):
  wbase2 (tuple_pad l H) = wbase2 l.
Proof. by rewrite tuple_pad_val wbase2_pad. Qed.

Lemma tuple_pad_injective k n (H: n <= k):
  injective (tuple_pad (n:=n) ^~ H).
Proof.
move => l1 l2 /= sv; apply:val_inj; move /eqP: (f_equal (fun l => tval l) sv).
by rewrite !tuple_pad_val eqseq_cat ?size_tuple // eqxx andbT => /eqP.
Qed.

Lemma wbase2_exists n k: log2 n <= k -> exists l:(k.-tuple 'I_3), wbase2 l = n.
Proof.
move => lk.
set l :=  [seq bool_to_I3 i | i<- (list_of_num (bin_of_nat n))]
      ++ (nseq (k - log2 n) ord0).
have sl: size l = k by rewrite /l size_cat size_map size_nseq -/(log2 n) subnKC.
exists (tcast sl (in_tuple l)).
by rewrite tcast_val  in_tupleE /l wbase2_pad wbase2_correct.
Qed.

Definition card_wbase2' k n := #|[set t :k.-tuple 'I_3 | wbase2 t == n ]|. 
Definition card_wbase2 n := card_wbase2' (log2 n) n.

Lemma card_wbase2_invariant k n : log2 n <= k -> 
  card_wbase2 n = card_wbase2' k n. 
Proof.
move => lk;move:(tuple_pad_injective (H:=lk)) => ti.
rewrite /card_wbase2 /card_wbase2' -(card_imset _ ti).
apply: eq_card => t; rewrite inE; apply/imsetP/idP.
  by move => [x]; rewrite inE => xp ->; rewrite wbase2_tuple_pad.
move => wtn.
have sizet: log2 n <= size t by rewrite size_tuple.
move:(wbase2_split sizet (eqP wtn)) => tv.
set x := take (log2 n) t .
have sx: size x = log2 n by  rewrite /= size_takel. 
set x' := tcast sx (in_tuple x).
have tv': t = tuple_pad x' lk.
  by apply:val_inj; rewrite /= tuple_pad_val tv  size_tuple !tcast_val.
by exists x' => //; rewrite inE // - {2}(eqP wtn) tv' wbase2_tuple_pad.  
Qed.

Lemma card_wbase2_odd n: card_wbase2 n.*2.+1 = card_wbase2 n.
Proof.
have sd:= (log2_Sdouble n).
rewrite (card_wbase2_invariant (leqnn (log2 n))).
rewrite (card_wbase2_invariant (leqnn (log2 n.*2.+1))) sd.
rewrite /card_wbase2'.
set T1 := (log2 n).-tuple 'I_3. 
set T2 := (log2 n).+1.-tuple 'I_3. 
have sz: forall z:T1, size (in_tuple (ord1_3::z)) = (log2 n).+1.
   by move => z;rewrite !size_tuple.
set g:(T1 -> T2) := (fun z => (tcast (sz z) (in_tuple (ord1_3::z)))).
have ig: injective g. move => z1 z2 ww; apply: val_inj.
    have: (tval (g z1) = tval (g z2)) by rewrite ww.
    by rewrite /g !tcast_val /=; case.
symmetry.
rewrite -(card_imset _ ig).
apply: eq_card => t; rewrite inE; apply/imsetP/idP.
  by move => [x]; rewrite inE => xp ->; rewrite /g tcast_val /= (eqP xp).
move=> /eqP /wbase2_odd1; move: (erefl (tval t)).
case: {-1} (tval t) => [ tv [] // | a l /= tv [av lv]]. 
have sl:(size (in_tuple l)) = log2 n. 
   by apply/eqP; rewrite -eqSS - (size_tuple t) tv.
exists (tcast sl (in_tuple l)); first by rewrite inE  tcast_val /= lv.
by apply: val_inj; rewrite /g /= tv av! tcast_val //.
Qed.

Lemma card_wbase2_even n: 
  card_wbase2 n.*2.+2 = card_wbase2 n +  card_wbase2 n.+1.
Proof.
move: (log2_double n); rewrite doubleS => ds.
set k := (log2 n.+1).
rewrite (card_wbase2_invariant (leqnn (log2 n.*2.+2))) ds -/k.
rewrite /card_wbase2'.
set T1 := k.-tuple 'I_3. 
set T2 := k.+1.-tuple 'I_3. 
set A := [set t:T2 | wbase2 t == n.*2.+2].
set B := [set t:T2 | (wbase2 t == n.*2.+2) && (head ord0 t == ord0)].
set C := [set t:T2 | (wbase2 t == n.*2.+2) && (head ord0 t == ord2_3)].
have dab: A :&: B = B. 
   by apply/setIidPr/subsetP => x; rewrite /A/B !inE => /andP[].
have dac: A:\: B = C.
   apply /setP => x; rewrite /A/B/C !inE; case ww:(wbase2 x == n.*2.+2) => //=.
   rewrite andbT; move: (wbase2_double_nz (eqP ww))=> [_].
   case ta: (head ord0 x == ord0); first by rewrite (eqP ta) //.
   by move/andP => [/eqP ->].
rewrite -(cardsID B A) dab dac addnC; congr addn; symmetry.
  have l2b:log2 n  <= k by apply: leqn_log.
  rewrite /C (card_wbase2_invariant l2b) /card_wbase2'.
  have sz: forall z:T1, size (in_tuple (ord2_3::z)) = k.+1.
    by move => z;rewrite !size_tuple.
  set g:(T1 -> T2) := (fun z => (tcast (sz z) (in_tuple (ord2_3::z)))).
  have ig: injective g. 
    move => z1 z2 ww; apply: val_inj.
    have: (tval (g z1) = tval (g z2)) by rewrite ww.
    by rewrite /g !tcast_val /=; case.
  rewrite -(card_imset _ ig).
  apply: eq_card => t; rewrite inE; apply/imsetP/idP.
    move => [x]; rewrite inE => xp ->.
    by rewrite /g tcast_val /= (eqP xp) add2n !eqxx //.
  move=> /andP[/eqP /wbase2_double_nz [tv]]; case:eqP; first by move => ->.
  move => _ /andP [sa sb] _.
  move /eqP: (f_equal size tv); rewrite size_tuple /= eqSS => /eqP sl1.
  have sl:(size (in_tuple (behead t))) = k  by rewrite /= -sl1.
  exists (tcast sl (in_tuple (behead t))); first by rewrite inE  tcast_val.
  by apply: val_inj; rewrite /g /= {1} tv (eqP sa) !tcast_val.
rewrite /C (card_wbase2_invariant (leqnn k)) /card_wbase2'.
have sz: forall z:T1, size (in_tuple (ord0::z)) = k.+1.
    by move => z;rewrite !size_tuple.
set g:(T1 -> T2) := (fun z => (tcast (sz z) (in_tuple (ord0::z)))).
have ig: injective g. 
  move => z1 z2 ww; apply: val_inj.
  have: (tval (g z1) = tval (g z2)) by rewrite ww.
  by rewrite /g !tcast_val /=; case.
rewrite -(card_imset _ ig).
apply: eq_card => t; rewrite inE; apply/imsetP/idP.
  move => [x]; rewrite inE => xp ->.
  by rewrite /g tcast_val /= (eqP xp) doubleS !eqxx.
move=> /andP[/eqP /wbase2_double_nz [tv ta tb]]. 
move: ta; rewrite tb (eqP tb) /= addbF => tc.
move /eqP: (f_equal size tv); rewrite size_tuple /= eqSS => /eqP sl1.
have sl:(size (in_tuple (behead t))) = k  by rewrite /= -sl1.
exists (tcast sl (in_tuple (behead t))); first by rewrite inE  tcast_val.
by apply: val_inj; rewrite /g /= {1} tv (eqP tb) !tcast_val.
Qed.

Lemma card_wbase2_val n: card_wbase2 n = fusc n.+1.
Proof.
have wz:card_wbase2 0 = fusc 1.
  rewrite /card_wbase2 /card_wbase2' /fusc /=.
  set T := (log2 0).-tuple 'I_3.
  suff: [set t:T | wbase2 t == 0] = [set t:T | predT t]. 
    by move => ->; rewrite cardsE /= card_tuple expn0.
   by apply /setP => t; rewrite ! inE; move: (size_tuple t); case: (tval t).
elim: n {-2} n (leqnn n) => [ []| n Hrec [|m]] //.
rewrite ltnS -(odd_double_half m);case:(odd _) => h.
  have la:=(leq_ltn_trans (double_le1 m./2) h).
  by rewrite add1n card_wbase2_even -doubleS fusc_odd (Hrec _ (ltnW la)) Hrec. 
rewrite add0n card_wbase2_odd - doubleS fusc_even Hrec //. 
exact (leq_trans (double_le1 m./2) h).
Qed.



End  WeakBaseTwoRepresentation.

  
Section SternBrocot.

Local Open Scope ring_scope.

Fixpoint SB_to_rat x := 
  match x with xH => 1
     | xO x' => Sba_i (SB_to_rat x')
     | xI x' => Sba_p (SB_to_rat x')
  end.

Lemma SB_to_rat_val n:
  SB_to_rat (pos_of_nat' n) = Stern (n.+1).
Proof.
rewrite - (bin_of_natK n.+1) /pos_of_nat' => /=.
elim: (pos_of_nat n n) => // p /= ->; rewrite  natTrecE - ?Stern_odd //.
move:(nat_of_pos_ne0 p); case: (nat_of_pos p) => // q _.
symmetry; apply:Stern_even.
Qed.


Definition natnat := (nat * nat)%type.
Delimit Scope nat_pair_scope with nat_pair.
Bind Scope nat_pair_scope with natnat.
Open Scope nat_pair_scope.

Definition pair_le a b:= (a.1 * b.2 <= a.2 * b.1)%N.
Definition pair_lt a b:= (a.1 * b.2 < a.2 * b.1)%N.
Definition good_pair a:= coprime a.1 a.2. 
Definition very_good_pair a:= [&& good_pair a, 0< a.1 & 0< a.2]%N.
Definition NaN := (0,0)%N. 

Notation "a <= b" := (pair_le a b): nat_pair_scope.
Notation "a < b" := (pair_lt a b): nat_pair_scope.

Lemma pair_le_bad a:  (a <= NaN) && (NaN <= a).
Proof. by rewrite /pair_le /= !muln0 !mul0n. Qed.

Lemma pair_le_bad' a:  ~~(a < NaN) && ~~(NaN < a).
Proof. by rewrite /pair_lt /NaN /= !muln0. Qed.

Lemma good_pair_prop a b:
  good_pair a -> good_pair b -> (a.1 * b.2 = a.2 * b.1)%N -> a = b.
Proof.
move => ga gb ea.
have : a.1 %| a.2 * b.1 by rewrite - ea /dvdn modnMr.
have : b.1 %|  a.1 * b.2 by rewrite  ea /dvdn modnMl.
rewrite  Gauss_dvdl //  Gauss_dvdr // => sa sb.
have r1:  a.1 = b.1 by apply/eqP; rewrite eqn_dvd sa sb.
rewrite (surjective_pairing a) (surjective_pairing b) r1.
suff: b.2 == a.2 by move/eqP  => ->.
move/eqP: ea; rewrite r1;case/posnP: b.1 => h; last by rewrite mulnC eqn_pmul2r.
by move: ga gb; rewrite /good_pair r1 h /coprime !gcd0n => /eqP -> /eqP ->.
Qed.

Lemma pair_le_nn a: a <= a.
Proof. by rewrite /pair_le mulnC leqnn. Qed.

Lemma pair_lt_nn a: (a < a) = false.
Proof. by rewrite /pair_lt mulnC ltnn. Qed.

Lemma pair_le_anti a b: good_pair a -> good_pair b -> 
  ((a <= b) && (b <= a)) = (a == b).
Proof.
rewrite /pair_le /= (mulnC b.2) (mulnC b.1) - eqn_leq => ga gb.
case: eqP; first by move/(good_pair_prop ga gb) => ->; rewrite eqxx.
by case: eqP => // ->; rewrite mulnC.
Qed.

Lemma pair_le_trans n m p: n != NaN ->
   m <= n -> n <= p -> m <= p.
Proof.
rewrite /pair_le => nz sa sb.
move:(leq_mul2r p.2 (m.1 * n.2) (m.2 * n.1)); rewrite sa orbT => sa'.
move:(leq_mul2l m.2 (n.1 * p.2) (n.2 * p.1)); rewrite sb orbT mulnA => sb'.
move: (leq_trans sa' sb'); rewrite mulnAC (mulnC n.2) mulnA leq_mul2r.
case dz: (n.2==0%N) => // _.
move: sb; rewrite (eqP dz) leqn0 muln_eq0; case/orP => /eqP hb. 
   move: sa; rewrite hb muln0 leqn0 muln_eq0 ; case/orP => /eqP hc. 
      by rewrite hc. 
   by move: nz; rewrite (surjective_pairing n) hb hc.
by rewrite hb muln0.
Qed.

Lemma pair_le_lt_trans n m p: m != NaN ->
   m <= n -> n < p -> m < p.
Proof.
rewrite  /pair_le /pair_lt =>  mz sa sb.
case: (posnP n.2) => n2z; first by move: sb; rewrite n2z ltn0.
case (posnP m.2) => m2z.
  move: sa; rewrite m2z leqn0 muln_eq0 (gtn_eqF n2z) orbF => m1z.
  by move: mz;  rewrite (surjective_pairing m) m2z (eqP m1z).
move:(leq_mul2r p.2 (m.1 * n.2) (m.2 * n.1)); rewrite sa orbT => sa'.
move: sb; rewrite - (ltn_pmul2l m2z) mulnA => sb'.
by move: (leq_ltn_trans sa' sb'); rewrite mulnAC (mulnC n.2) mulnA ltn_pmul2r.
Qed.

Lemma pair_lt_le_trans n m p: p != NaN ->
   m < n -> n <= p -> m < p.
Proof.
rewrite  /pair_le /pair_lt => pz sa sb.
move:(leq_mul2l m.2 (n.1 * p.2) (n.2 * p.1)); rewrite sb orbT mulnA => sb'.
case: (posnP m.2) => m2z; first by move: sa; rewrite m2z ltn0.
case: (posnP n.1) => n1z; first by move: sa; rewrite n1z muln0 ltn0.
case: (posnP p.1) => p1z. 
   move:sb; rewrite p1z muln0 leqn0  muln_eq0  (gtn_eqF n1z) /= => ww.
  by move: pz; rewrite (surjective_pairing p) p1z (eqP ww).
case: (posnP p.2) => p2z; first by rewrite p2z muln0 muln_gt0 m2z p1z.
case: (posnP n.2) => n2z.
  by move: sb; rewrite n2z leqn0 muln_eq0 (gtn_eqF p2z) (gtn_eqF n1z).  
move: sa; rewrite - (ltn_pmul2r p2z) => sa'.
by move:(leq_trans sa' sb'); rewrite mulnAC (mulnC n.2) mulnA ltn_pmul2r.
Qed.

Lemma pair_lt_trans n m p: m < n -> n < p -> m < p.
Proof.
rewrite {1} /pair_lt ltn_neqAle => /andP [ha hb] hc.
case hd: (m== NaN); last apply: (pair_le_lt_trans (negbT hd) hb hc). 
by move: ha; rewrite (eqP hd).
Qed.

Lemma pair_lt_le a b:  good_pair a -> good_pair b -> 
  a < b = (a <= b) && (a != b).
Proof.
move => sa sb.
rewrite /pair_lt /pair_le ltn_neqAle andbC.
case:eqP =>h; first by rewrite (good_pair_prop sa sb h) eqxx.
by case:eqP => eab //; move:h; rewrite eab mulnC.
Qed.

Lemma pair_lt_trichot a b:  good_pair a -> good_pair b -> 
  (a < b) (+) (b < a) (+) (a == b).
Proof.
move => pa pb.
rewrite  -(pair_le_anti pa pb).
rewrite /pair_le/pair_lt (mulnC b.1) (mulnC b.2).
set x := (a.1 * b.2)%N; set y := (a.2 * b.1)%N.
by rewrite (leq_eqVlt x)(leq_eqVlt y) eq_sym; case:(ltngtP y x).
Qed.
 

Definition area a b := (a.2)%:Z * (b.1)%:Z - (a.1)%:Z * (b.2)%:Z.

Lemma area_sym a b : area a b = - (area b a).
Proof. by rewrite /area opprD addrC mulrC opprK (mulrC (b.1)%:Z). Qed.

Lemma area_xx a : area a a = 0.
Proof. by rewrite /area mulrC subrr. Qed.

Lemma area_gt0 a b: (a < b) = (0 < area a b)%R.
Proof. by rewrite /area subr_gt0. Qed.

Lemma area_ge0 a b: (a <= b) = (0 <= area a b)%R.
Proof. by rewrite /area subr_ge0. Qed.

Lemma area_eq0 a b: good_pair a -> good_pair b ->
   (area a b) == 0 -> a = b.
Proof. 
move => sa sb; rewrite eqr_le {1} area_sym oppr_le0 - !area_ge0 => h.
by move:(esym(pair_le_anti sb sa)); rewrite h => /eqP ->.
Qed.

Definition pair_near a b := area a b == 1.

Lemma pair_nearE a b: (pair_near a b) = (a.2 * b.1 == a.1 * b.2 +1)%N. 
Proof.
by rewrite /pair_near/area - eqz_nat subr_eq addrC PoszD !PoszM.
Qed.

Lemma pair_near_good a b: pair_near a b -> good_pair a && good_pair b.
Proof.
rewrite pair_nearE => /eqP H.
apply/andP; split; last exact:(coprime_if_bezout H).
by move:H; rewrite mulnC (mulnC a.1) => /coprime_if_bezout; rewrite coprime_sym.
Qed.

Definition pair_add a b := (a.1 + b.1, a.2 + b.2)%N.
Notation "a + b" := (pair_add a b): nat_pair_scope.

Lemma pair_addC a b: a + b = b + a.
Proof. by rewrite /pair_add addnC (addnC a.2). Qed.

Lemma pair_add_monotone a b: a <= b ->  (a <= a + b) && (a + b <= b).
Proof.
rewrite /pair_add /pair_le /= => h.
by rewrite  !mulnDr !mulnDl  mulnC leq_add2l h (mulnC b.1)  leq_add2r h. 
Qed.

Lemma pair_add_smonotone a b: a < b -> (a < a + b) && (a + b < b).
Proof.
rewrite /pair_add /pair_lt /= => h.
by rewrite  !mulnDr !mulnDl  mulnC ltn_add2l h (mulnC b.1)  ltn_add2r h. 
Qed.

Lemma area_Dr a b b': area a (b+b') = ((area a b) + (area a b'))%R.
Proof.
by rewrite /area /pair_add /= !PoszD !mulrDr addrACA opprD.
Qed.

Lemma area_Dl a a' b: area (a+a') b = ((area a b) + (area a' b))%R.
Proof. by rewrite area_sym area_Dr opprD - !area_sym. Qed.

Lemma add_near_l a b: pair_near a b -> pair_near a (a+b).
Proof. by rewrite /pair_near area_Dr area_xx add0r. Qed.

Lemma add_near_r a b: pair_near a b -> pair_near (a+b) b.
Proof. by rewrite /pair_near area_Dl area_xx addr0. Qed.

Lemma add_near_g a b: pair_near a b -> good_pair (a+b).
Proof. by move => /add_near_r /pair_near_good /andP []. Qed.

Definition areaN a b := (a.2 * b.1 - a.1 * b.2) %N.
Definition pair_dist x a b:= (areaN a x + areaN x b) %N.

Lemma areaN_lt a b: a < b -> (areaN a b)%:Z = area a b.
Proof.
rewrite /areaN /area => /ltnW h; apply: (addrI (a.1 * b.2)%:Z).
by rewrite - PoszD subnKC // -!PoszM addrA addrC addKr.
Qed.

Lemma pair_distl x a b: a < b -> a < x -> x < a + b -> 
  (pair_dist x a (a+b)%nat_pair < pair_dist x a b) %N.
Proof.
move => lab sa sb.
move:(pair_add_smonotone lab) => /andP [_ sc]; move:(pair_lt_trans sb sc) => sd.
have: pair_dist x a (a + b) = areaN x b :> int.
  by rewrite /pair_dist areaN_lt // PoszD !areaN_lt // area_Dr area_sym addKr.
by case => ->; apply: ltn_paddl; rewrite/areaN subn_gt0.
Qed.

Lemma pair_distr x a b: a < b -> a + b < x -> x < b -> 
  (pair_dist x (a+b) %nat_pair b < pair_dist x a b) %N.
Proof.
move => lab sa sb.
move:(pair_add_smonotone lab) => /andP [sc]; move:(pair_lt_trans sc sa) => sd _.
have: pair_dist x (a + b) b = areaN a x :> int.
  by rewrite /pair_dist areaN_lt//PoszD !areaN_lt// area_Dl (area_sym x) addrK.
by case => ->;apply: ltn_paddr; rewrite/areaN subn_gt0.
Qed.

Fixpoint SB_rec n x a b p :=
    if n is n'.+1 then
     if (x < a + b) then SB_rec n' x a (a+b) (xO p)
     else if (a + b < x) then SB_rec n' x (a+b) b (xI p)
     else p
    else p.

Definition SB_val x := let a := (0%N,1%N) in let b := (1%N,0%N) in
   SB_rec (pair_dist x a b) x a b xH.

(*


CoInductive SB_tree: Set := 
  mk_SB_tree:  rat -> SB_tree -> SB_tree -> SB_tree. 

CoFixpoint CW (x: rat): SB_tree := mk_SB_tree x (CW (Sba_p x)) (CW (Sba_i  x)).
Definition CW1 := CW 1%Q.

*)

(* 4 / 7 
Eval compute in  (SB_to_rat (xO (xI (xO (xO xH))))).

*)

End SternBrocot.


Fixpoint fuscP2 p :=
   match p with 
   | xO n => let: (a,b) := fuscP2 n in (a, a+b)
   | xI n => let: (a,b) := fuscP2 n in (a+b,b)
   | xH => (1,1)
end.

Definition fuscN2 p := if p is (Npos p) then (fuscP2 p) else (0,1).

Lemma fuscN2_prop n:
  fuscN2 (bin_of_nat n) = (fusc n, fusc n.+1).
Proof.
case: n => [// | n]; rewrite - {2 3}(bin_of_natK n.+1) - nat_of_succ_gt0 /=.
elim: (pos_of_nat _ _).
+ by move => p /= ->; rewrite /= !natTrecE fusc_even fusc_odd nat_of_succ_gt0.
+ by move => p /= ->; rewrite /= !natTrecE fusc_even fusc_odd nat_of_succ_gt0.
+ done.
Qed.

Lemma fuscN_prop n: fusc n = (fuscN2 (bin_of_nat n)).1.
Proof. by rewrite fuscN2_prop. Qed.


(** * The Stern Diatomic sequence *)


Fixpoint sternd_rec s : seq nat :=
  if s is a :: s1 then if s1 is  b :: _ then [:: a, a+b & sternd_rec s1]
  else  [:: a] else nil.

Fixpoint sternD (u v n : nat) :=
  if n is k.+1 then sternd_rec (sternD u v k) else  [:: u; v].

Definition stern11 := sternD 1 1. 
Definition stern01 := sternD 0 1. 
Definition stern i := nth 0 (stern01 i) i.

Lemma stern_ex1 m n: sternD m n 1 = [:: m; m+n ; n].
Proof. done. Qed.

Lemma stern_ex2 m n: sternD m n 2 = [:: m; 2 * m +n; m + n ; m + 2 *n; n].
Proof. by rewrite /= addnA addnn -addnA addnn -!mul2n. Qed.

Lemma stern_ex3 m n: 
  sternD m n 3 = 
  [:: m; 3*m + n; 2*m+n; 3*m+2*n; m+n;  2*m+3*n; m + 2*n; m+3*n ; n].
Proof. 
simpl.
have ->:  m + (m + n) = 2* m + n  by rewrite addnA  addnn mul2n.
have ->: m + n + n = m + 2 * n by rewrite - addnA addnn mul2n.
rewrite addnA addnACA (addnC _ m) - (mulSn 2 m)  addnn - mul2n.
by rewrite addnACA addnn - mul2n -addnA (addnC (2*n) n) - (mulSn 2 n).
Qed.

Lemma size_sternD u v n: size (sternD u v n) = (2^n).+1.
Proof.
elim:n => // n Hr.
rewrite expn2S - [RHS] /(((2 ^ n).+1).*2.-1) - Hr /=.
by elim: (sternD u v n) => // c [] // d l /= ->.
Qed.

Lemma head_sternD u v n: head 0 (sternD u v n) = u.
Proof. by elim:n => // n {2} <- /=; case:(sternD u v n) => // [] c []. Qed.

Lemma last_sternD u v n: last 0 (sternD u v n) = v.
Proof.
by elim:n => // n /= {2} <-; elim:(sternD u v n) => // c; case => // d; case.
Qed.

Lemma sternD_split1 u v n: sternD u v n = u :: behead (sternD u v n). 
Proof.
rewrite -{2} (head_sternD u v n);move: (size_sternD u v n).
by case:(sternD u v n). 
Qed.

Lemma sternD_split2 u v n: sternD u v n = 
   rcons (belast u (behead (sternD u v n))) v.
Proof.
by rewrite - {3} (last_sternD u v n) {1 3}(sternD_split1 u v n) - lastI.
Qed.

Lemma sternd_rec_aux a s:
  s != nil -> sternd_rec (a::s) = [:: a, (a + head 0 s) & sternd_rec s].
Proof. by case: s. Qed.


Lemma sternD_rev u v n:  sternD v u n = rev (sternD u v n).
Proof. 
elim:n => //n /= ->; move:(sternD u v n); apply: last_ind => //[] [] // a l x h.
have sa: rev (a :: l) != nil by rewrite split_rev.
have ww: sternd_rec (rcons (a :: l) x) =
    rcons (rcons (sternd_rec (a :: l)) ((last 0 (a :: l)) + x)) x.
  by clear;elim: l a x  => // c s Hr a d; rewrite ! rcons_cons - Hr rcons_cons.
by rewrite rev_rcons (sternd_rec_aux _ sa) addnC h ww ! rev_rcons head_rev.
Qed.

Lemma stern11_symmetric n: rev (stern11 n) = (stern11 n).
Proof. by rewrite - (sternD_rev). Qed.

Notation "x ++- y" :=  (x ++ behead y) (at level 60).

Lemma split_sternD u v n :
  (sternD u v n.+1) = (sternD u (u + v) n) ++- (sternD (u + v) v n).
Proof.
elim:n => // n /=  ->.
rewrite (sternD_split1 (u+v) v n) (sternD_split2 u (u+v) n) [LHS]/=.
set A := belast _ _; set B := behead _; elim: A (u+v); first by case:B.
move => a l Hr b.
have ha: rcons l b != [::] by case l.
have hc: rcons l b ++ B != [::] by case l.
have hb: head 0 (rcons l b ++ B) = head 0 (rcons l b) by case l.
by rewrite rcons_cons cat_cons (sternd_rec_aux _ hc)(sternd_rec_aux _ ha) Hr hb.
Qed.

Lemma split_sternD_left u v n :
  take ((2^n).+1) (sternD u v n.+1) = sternD u (u + v) n.
Proof. by rewrite split_sternD; rewrite take_size_cat // size_sternD. Qed.


Lemma split_sternD_right u v n :
  drop (2^n) (sternD u v n.+1) = sternD (u + v) v n.
Proof. 
rewrite split_sternD sternD_split2 {2} (sternD_split1 (u+v)) cat_rcons.
by rewrite drop_size_cat // size_belast size_behead size_sternD.
Qed.

Lemma split_stern01_left n : take ((2^n).+1) (stern01 n.+1) = stern01 n.
Proof. by rewrite split_sternD_left add0n. Qed.

Lemma split_stern01_right n : drop (2^n) (stern01 n.+1) = stern11 n.
Proof. by rewrite split_sternD_right. Qed.

Lemma sternD_nth_even u v n k:
  nth 0 (sternD u v n.+1) (k.*2) = nth 0 (sternD u v n) k.
Proof.
rewrite /sternD -/sternD; move: {u v n} (sternD u v n).
elim:k; first by case => // a;case.
by move => n Hrec [] // a [ | b l ]; rewrite /= ? nth_nil -? (Hrec (b::l)). 
Qed.

Lemma sternD_nth_odd u v n k:
  k < 2^n ->
  nth 0 (sternD u v n.+1) (k.*2.+1) = 
  nth 0 (sternD u v n) k + nth 0 (sternD u v n) k.+1.
Proof.
rewrite {1} /sternD -/(sternD ) - ltnS -(size_sternD u v n).
move: {u v n} (sternD u v n); elim:k; first by case => // a; case.
move => n Hrec [] // a [] // b l; rewrite ltnS => ww;apply: (Hrec (b:: l) ww).
Qed.


Lemma stern_prop i j: i <= 2^j ->  nth 0 (stern01 j) i = stern i.
Proof.
have rec k n: k <= 2^n -> nth 0 (stern01 n.+1) k = nth 0 (stern01 n) k.
   by move => h; rewrite - (split_stern01_left n);rewrite nth_take //.
move => le1; case /orP: (leq_total i j) => le2. 
  rewrite -(subnK le2); elim:(j-i) => //  k Hrec; rewrite addSn rec //. 
  by apply: leq_trans (ltnW (cantor (k+i))); rewrite leq_addl.
rewrite /stern -{2}  (subnK le2); elim: (i -j) => // k Hrec.
by rewrite addSn rec ? Hrec // (leq_trans le1) // leq_exp2l //leq_addl.
Qed.

Lemma nth_stern11 n i: i <= 2^n -> 
    nth 0 (stern11 n) i = stern (2^n + i).
Proof.
move => h.
by rewrite - split_stern01_right nth_drop stern_prop // expn2S -addnn leq_add2l.
Qed.

Lemma nth_stern11_sym n i: i <= 2 ^n ->
  nth 0 (stern11 n) i = stern (2^n.+1 - i).
Proof.
move => H;rewrite -stern11_symmetric nth_rev size_sternD ?ltnS // subnS subSKn.
by rewrite nth_stern11 ? leq_subr// addnBA // addnn expn2S.
Qed.

Lemma stern_fusc: fusc_prop stern.
Proof.
split => //.
  case => // n.
  have h := (leq_ltn_trans (leqW (double_le1 n)) (cantor n.*2.+1)).
  rewrite {1} /stern {1} doubleS sternD_nth_even;apply: (stern_prop h). 
move => n. 
move: (leq_ltn_trans (double_le1 n) (ltn_expl n.*2 (ltnSn 1))) => ha.
rewrite {1} /stern sternD_nth_odd // -/(stern01 _).
by rewrite (stern_prop (ltnW ha)) stern_prop.
Qed.

Lemma sternD_fusc: stern =1 fusc.
Proof. apply: (fusc_unique stern_fusc fusc_rec). Qed.


Definition add_seq s1 s2 := [seq x.1 + x.2 | x <- zip s1 s2].
Definition sub_seq s1 s2 := [seq x.1 - x.2 | x <- zip s1 s2].
Definition scale_seq k s := [seq k * x | x <- s].

Lemma scale_sternD k a b n: 
  sternD (k*a) (k*b) n = scale_seq k (sternD a b n).
Proof.
elim: n=> // n /= ->.
by elim: (sternD a b n)=> // c [] // d l Ihl /=; rewrite mulnDr -Ihl.
Qed.

Lemma add_sternD a b c d n: 
  sternD (a + c) (b + d) n = add_seq (sternD a b n) (sternD c d n).
Proof.
elim: n=> // n /= ->.
have: size (sternD a b n) == size (sternD c d n) by rewrite !size_sternD.
move: (sternD a b n)(sternD c d n); apply: seq2_ind => // e f []; first by case.
move=> g l1 [] // h l2.
by rewrite /= -/(sternd_rec (h::l2)) -/(sternd_rec (g::l1)) addnACA => ->.
Qed.

Lemma sub_sternD a b c d n: c <= a -> d <= b ->
  sternD (a - c) (b - d) n = sub_seq (sternD a b n) (sternD c d n).
Proof.
set x := (sternD (a - c) (b - d) n). 
move => ha hb;rewrite - (subnKC ha) - (subnKC hb) add_sternD -/x. 
have: size x == size (sternD c d n) by rewrite !size_sternD.
move: x (sternD c d n); apply: seq2_ind => // e f s1 s2.
by rewrite /sub_seq /= addKn => {1} ->.
Qed.

Lemma stern_equation5 n: sub_seq (sternD 1 2 n) (stern11 n) = stern01 n.
Proof. by rewrite -sub_sternD. Qed.

Lemma sternD_col_progression n i : i <= 2^n -> 
  nth 0 (stern11 n.+1) i =  nth 0 (stern11 n) i + stern i.
Proof.
move => lin.
have s1: size (stern01 n) = (2 ^n).+1 by rewrite size_sternD.
have s2: size (stern11 n) = (2 ^n).+1 by rewrite size_sternD.
have s3: size (sternD 0 1 n) = size (sternD 1 1 n) by rewrite s1 s2.
have ib2 : i < size (zip (stern01 n) (stern11 n)).
  by rewrite size_zip s1 s2 minnn.
transitivity (nth 0 (sternD 1 2 n) i).
  by rewrite - (split_sternD_left 1 1 n) nth_take.
rewrite (add_sternD 0 1 1 1 n) /add_seq (nth_map (0, 0)) //. 
by rewrite nth_zip // addnC stern_prop.
Qed.


Lemma arith_split_sternD u v n:
   sternD u v n = 
   add_seq (scale_seq u (rev (stern01 n))) (scale_seq v (stern01 n)).
Proof.
rewrite - {1} (addn0 u) - {1} (add0n v) add_sternD.
by rewrite - scale_sternD - sternD_rev - scale_sternD !muln0 ! muln1.
Qed.

Lemma sternD_stern u v n i: i <= 2^n ->
  nth 0  (sternD u v n) i = u * (stern (2^n - i)) + v * (stern i).
Proof.
move => sa.
rewrite arith_split_sternD.
have kl1: i < (2 ^ n).+1 by rewrite ltnS.
set l1 := scale_seq _ _; set l2 := scale_seq _ _.
have sl1: size l1 = (2^n).+1.
  by rewrite /l1 - sternD_rev - scale_sternD size_sternD.
have sl2: size l2 = (2^n).+1 by rewrite /l2 - scale_sternD size_sternD.
have sl1l2: size l1 = size l2 by rewrite sl1 sl2.
have k1: i < size (stern01 n) by rewrite size_sternD.
have k2: i < size (rev (stern01 n)) by rewrite - sternD_rev size_sternD.
have kz: i < size (zip l1 l2) by rewrite size_zip sl1 sl2 minnn.
rewrite /add_seq (nth_map (0,0) _ _ kz) // nth_zip //=.
rewrite /l1 /scale_seq (nth_map 0 _ _ k2) /l2 /scale_seq (nth_map 0 _ _ k1).
rewrite (nth_rev _ k1)  {2} /stern01 size_sternD subSS.
by rewrite stern_prop ?leq_subr // (stern_prop sa).
Qed.

Lemma sternD_01_positive n i:
  0 < nth 1 (sternD 0 1 n) i.+1.  
Proof.
elim:n i; first by case => //; case.
move => n; rewrite/sternD -/(sternD); elim:(sternD 0 1 n) => // a.
case => // b l Hrec aux; have bp := (aux 0).
case; [by rewrite /= addn_gt0 bp orbT | case; [ by case l | move => k]]. 
apply: Hrec => j; exact: (aux j.+1).  
Qed.

Lemma stern_gt0 k: (0 < stern k) = (0 < k).
Proof. 
case: k => // k.
have-> : stern k.+1 = nth 1 (stern01 k.+1) k.+1.
  apply:set_nth_default; rewrite size_sternD ltnS ltnW //; apply:cantor.
by rewrite (sternD_01_positive) lt0n.
Qed.


Lemma sternD_ge_in_bounds u v n i: 0 < i < 2^n ->
  u + v <= nth 0 (sternD u v n) i.  
Proof.
move => /andP[ka kb]; rewrite (sternD_stern _ _ (ltnW kb)).
by apply: leq_add; apply:leq_pmulr; rewrite stern_gt0 // subn_gt0.
Qed.


Lemma sternD_at_bounds u v n :
  nth 0 (sternD u v n) 0 = u /\ nth 0 (sternD u v n) (2^n) = v.
Proof.
rewrite nth0 head_sternD.
by rewrite  -(succnK (2^n)) -(size_sternD u v n) nth_last last_sternD.
Qed.


Lemma nth_stern11_alt n i: i <= 2^n ->
  nth 0 (stern11 n) i = stern (2^n - i) + stern i.
Proof. by move => h; rewrite (sternD_stern) // !mul1n. Qed.

Lemma sternD_bound1 i n: i <= 2 ^n ->
  stern i <= (nth 0 (stern11 n) i) ?= iff (i == 2 ^ n).
Proof.
move => ha; rewrite nth_stern11_alt //.
apply/leqifP; case hb: (i == 2 ^ n);first by rewrite (eqP hb) subnn add0n eqxx.
by apply/ltn_paddl; rewrite stern_gt0 subn_gt0  ltn_neqAle ha hb. 
Qed.

Lemma sternD_bound2 n i: i <= 2 ^ n ->
  nth 0 (stern11 n.+1) i <=  (nth 0 (stern11 n) i).*2 ?= iff (i==2^n).
Proof.
move => ha.
rewrite (sternD_col_progression ha) - addnn.
set f := addn (nth 0 (stern11 n) i).
have hb: {mono f : m n / m <= n} by move => u v /=; rewrite /f leq_add2l.
by rewrite (mono_leqif hb) //; apply: sternD_bound1.
Qed.


Lemma sternD_positive u v n i : 0 < u -> 0 < v -> i <= 2^n ->
   0 < nth 0 (sternD u v n) i.
Proof.
move: (sternD_at_bounds u v n) => [sa sb] ap bp kn.
case l2: (0 < i < 2^n).
  apply: (leq_trans _ (sternD_ge_in_bounds u v l2)).
  by rewrite (addn_gt0 u v) ap bp.
move: (negbT l2); rewrite negb_and - leqNgt leqn0 ltn_neqAle kn andbT /= negbK. 
by case /orP; move/ eqP ->; rewrite ? sa ?sb. 
Qed.

Lemma sternD_middle u v n : nth 0 (sternD u v n.+1) (2^n) = u + v.
Proof.
rewrite split_sternD nth_cat size_sternD /= ltnS leqnn.
exact: (proj2 (sternD_at_bounds u (u + v) n)).
Qed.

Lemma sternD_middle_contra u v n i : u != 0 -> v != 0 ->
   nth 0 (sternD u v n.+1) i = u + v -> i = 2 ^ n.
Proof.
move => /negbTE anz /negbTE bnz /eqP; rewrite eq_sym.
move:(sternD_at_bounds u v  n.+1) => [sa sb].
case kz: (i == 0); first by rewrite (eqP kz) sa -{2} (addn0 u) eqn_add2l bnz.
case: (ltngtP i (2^n)) => // kl2.
  rewrite split_sternD nth_cat size_sternD ltnS (ltnW kl2) => /eqP Hk.
  have kl3: (0< i < 2^n) by rewrite lt0n  kl2 kz. 
  move: (sternD_ge_in_bounds u (u + v) kl3).
  by rewrite - Hk - {2} (add0n (u + v)) leq_add2r leqn0 anz.
case: (ltngtP i (2^n.+1)) => kl1; last first. 
    by rewrite kl1 sb -{2} (add0n v) eqn_add2r anz.
  by rewrite (nth_default)  ?size_sternD // addn_eq0 anz bnz.
rewrite split_sternD nth_cat size_sternD ltnS leqNgt kl2 nth_behead => /eqP Hk.
move: kl1; rewrite -(subnK kl2) addnS -addSn expnS mul2n -addnn ltn_add2r => lt.
have kl3: 0 < (i - (2 ^ n).+1).+1 < 2 ^n by rewrite lt.
move: (sternD_ge_in_bounds (u+v) v kl3).
by rewrite -Hk - {2} (addn0 (u+v)) leq_add2l leqn0 bnz.
Qed.

Lemma sternD_nth_compare u v n i (S := (sternD u v n.+1)):
  i < 2^n -> maxn (nth 0 S (i.*2)) (nth 0 S (i.*2.+2)) <= nth 0 S (i.*2.+1).
Proof.
move=> h; have:= (sternD_nth_odd u v h).
by rewrite - doubleS ! sternD_nth_even=> ->; rewrite geq_max leq_addr leq_addl.
Qed.

Lemma sternD_nth_compare_strict u v n i (S := (sternD u v n.+1)) :
   0 < u -> 0 < v -> i < 2^n -> 
   maxn  (nth 0 S (i.*2)) (nth 0 S (i.*2.+2)) < nth 0 S (i.*2.+1).
Proof.
move=> ap bp h.
move: (sternD_nth_odd u v h); rewrite - doubleS ! sternD_nth_even  => ->.
move: (sternD_positive ap bp (ltnW h)) (sternD_positive ap bp h) => sa sb.
by rewrite gtn_max ltn_paddl // ltn_paddr.
Qed.

Lemma sternD_nth_compare_rec u v n i: 
   0 < u -> 0 < v -> i.*2 < 2^n -> 
   n < nth 0 (sternD u v n) i.*2.+1.
Proof.
move => sa sb;elim: n i. 
  move => k; rewrite ltnS (leq_double k 0) leqn0 => /eqP -> //.
move => n Hrec k; rewrite expn2S ltn_double => ha.
move: (sternD_nth_compare_strict sa sb ha).
rewrite - doubleS !sternD_nth_even gtn_max; move/andP => [hc hd].
case: (odd_dichot k) => k1; rewrite k1 in ha.
  by apply: leq_trans hc; rewrite ltnS k1; apply: Hrec; apply: ltnW. 
by apply: leq_trans hd; rewrite ltnS k1; apply: Hrec.
Qed.

Definition sternD_sum u v n := \sum_(i <- (sternD u v n)) i.

Lemma sternD_sumE u v n :  sternD_sum u v n = ((3^n).+1)./2 * (u + v).
Proof.
elim:n u v.
  by move => a b;rewrite /sternD_sum ! big_cons big_nil addn0 mul1n.
rewrite /sternD_sum =>n Hrec a b;apply/eqP. 
move:(Hrec (a+b) b); rewrite {1} sternD_split1  big_cons addnC => eq1.
have o3n: odd (3 ^ n) by elim n => // q hr; rewrite expnS odd_mul hr.
rewrite - (eqn_add2r (a + b)) - mulSnr expnS split_sternD big_cat Hrec - addnA.
rewrite eq1 - mulnDr  (addnA a) addnn - (addnA a) addnn addnACA.
rewrite - mul2n - mulSnr - mul2n - mulSn - mulnDr mulnA (mulnC _ 3).
rewrite - [_ ./2.+1]/(((3 * 3^n).+3) ./2)  - (addn3 (3 * 3 ^ n)) -  mulnSr.
rewrite - {2} (odd_double_half ((3 ^ n).+1)) /odd -/odd o3n.
by rewrite - muln2 mulnA muln2 doubleK. 
Qed.

Lemma sternD_sumC u v n : sternD_sum u v n = sternD_sum v u n.
Proof. by rewrite !sternD_sumE addnC. Qed.


Lemma sternD_sum_quo a b a' b' n :  
  ((sternD_sum a b n) %:Q / (sternD_sum a' b' n) %:Q) %R =
   ((a +b)%nat%:Q / ((a'+b')%nat%:Q))%R .
Proof.
rewrite !sternD_sumE !ratN_M  - mulf_div divff ?mul1r // intr_eq0.
by move:(expn_eq0 3 n);case: ((3 ^ n)%nat).
Qed.


Lemma sternD_sum_lin a b a' b' n :  
  (sternD_sum a b n) +(sternD_sum a' b' n) =  sternD_sum (a+a') (b+b') n.
Proof.  by rewrite !sternD_sumE -mulnDr addnACA. Qed.

Lemma head_sternD' n: head 0 (stern11 n) = 1.
Proof. apply: head_sternD. Qed.

Lemma last_sternD' n: last 0 (stern11 n) = 1.
Proof. apply: last_sternD. Qed.

Lemma SternD_positive' n k: 0 < k < 2^n -> 1 < nth 0 (stern11 n) k.
Proof. move => h; exact: (sternD_ge_in_bounds 1 1 h). Qed.

Lemma sternD_middle' n : nth 0 (stern11 n.+1) (2^n) = 2.
Proof. by apply:sternD_middle. Qed.

Lemma sternD_middle_contra' n k : nth 0 (stern11 n.+1) k = 2 -> k = 2 ^ n.
Proof. by apply:sternD_middle_contra. Qed.

Lemma sternD_middle_quo u v k q n (i:= 2^k * (q.*2.+1)) (S := sternD u v n):
  i < 2^n -> nth 0 S i.-1 + nth 0 S i.+1 = (k.*2.+1) * (nth 0 S i).
Proof.
rewrite /i /S; clear => h.
have ha: k < n. 
  by rewrite -(ltn_exp2l k n (ltnSn 1));apply: leq_ltn_trans h;apply:leq_pmulr.
move: h.
rewrite - (subnK ha); set m := _ - _; rewrite -addSnnS.
rewrite addnC expnD ltn_pmul2l ? expn_gt0 // -doubleS expn2S leq_double => h.
clear ha;move: m h; elim: k q => [q m lqm | k Hrec q m lqm].
  by rewrite add0n !mul1n - doubleS !sternD_nth_even sternD_nth_odd.
set i := (2 ^ k * q.*2.+1).
have ha: i< 2 ^ (k + m.+1).
  by rewrite /i expnD ltn_pmul2l ? expn_gt0 // -doubleS expn2S leq_double.
have hb:= (leq_ltn_trans (leq_pred i) ha).
have ip: 0 < i by rewrite muln_gt0 expn_gt0.
have eq1: i.*2.-1 = (i.-1).*2.+1 by rewrite -{1} (prednK ip) doubleS.
rewrite addSn expn2S - doubleMl  sternD_nth_even sternD_nth_odd // eq1.
rewrite sternD_nth_odd // (prednK ip)  (addnC (nth _ _ i)) addnACA.
by rewrite Hrec //  addnA - mulSnr - mulSnr doubleS.
Qed.

Lemma sternD_middle_div u v i n  (S := sternD u v n):
  0 < i < 2^n -> (nth 0 S i) %|  (nth 0 S i.-1 + nth 0 S i.+1).
Proof.
move /andP=> [h1].
case:(elogn2P i.-1) => k q; rewrite (prednK h1) => -> sa.
by rewrite sternD_middle_quo // -/S /dvdn modnMl.
Qed.

Lemma sternD_odd_rec u v k q n (i:= 2^k * (q.*2.+1)) (S := sternD u v n):
  i < 2^n -> odd (nth 0 S i) ->  odd(nth 0 S i.-1 + nth 0 S i.+1).
Proof.
by move => h1 h2; rewrite (sternD_middle_quo _ _ h1) odd_mul /= odd_double.
Qed.

Lemma sternD_gcd_succ u v i n  (S := sternD u v n):
  0 < i < 2^n -> 
  gcdn (nth 0 S i.-1) (nth 0 S i) = gcdn (nth 0 S i)(nth 0 S i.+1).
Proof.
move => h.
move: (sternD_middle_div u v h).
set b := nth _ _ _; set a := nth _ _ _; set c := nth _ _ _ => /dvdnP [k ks].
have ea: c = k* b - a by rewrite - ks addKn.
have lab: a <= k * b by rewrite -ks leq_addr.
have eb: a = k* b - c by rewrite - ks addnK.
have lac: c <= k * b by rewrite -ks leq_addl.
move: (dvdn_gcdr a b) (dvdn_gcdl a b) => da db.
move: (dvdn_gcdr b c) (dvdn_gcdl b c) => dc dd.
have ha: gcdn a b %| k * b by rewrite dvdn_mull.
apply/eqP; rewrite eqn_dvd ! dvdn_gcd da dd {1} ea dvdn_subr // db.
by rewrite eb dvdn_subr // ? dc // dvdn_mull.
Qed.

Lemma sternD_gcd_rec u v i n  (S := sternD u v n):
   i < 2^n -> 
  gcdn (nth 0 S 0) (nth 0 S 1) = gcdn (nth 0 S i)(nth 0 S i.+1).
Proof.
elim: i => //i Hrec h1.
have sa :0 < i.+1 < 2 ^ n by rewrite h1.
by rewrite (Hrec (ltnW h1)) -(sternD_gcd_succ _ _ sa).
Qed.

Lemma sternD_gcd_rec2 u v i n  (S := sternD u v n):
   i < 2^n -> gcdn (nth 0 S i)(nth 0 S i.+1) = gcdn u v.
Proof.
move => h; rewrite -(sternD_gcd_rec u v h).
by rewrite nth0 head_sternD sternD_stern ? expn_gt0 // muln1 mulnC gcdnMDl.
Qed.

Lemma sternD_consecutive_coprime1 i n  (S := stern11 n):
   i < 2^n -> coprime (nth 0 S i)(nth 0 S i.+1).
Proof.
by move => h; rewrite /coprime (sternD_gcd_rec2 1 1 h).
Qed.

Lemma sternD_coprime_succ_add i n  (S := stern11 n)
  (a := nth 0 S i.-1)(b := nth 0 S i)(c := nth 0 S i.+1):
  0 < i < 2 ^n -> b = a + c -> coprime a c.
Proof.
move => /andP[ha hb].
move:(sternD_consecutive_coprime1 hb) => sa sb.
by move: sa; rewrite /coprime -/stern11 -/b sb  gcdnC gcdnDr gcdnC.
Qed.

Lemma Stern_pair_injective i n j m:
   i < 2^n -> j < 2^m -> 
  nth 0 (stern11 n) i = nth 0 (stern11 m) j ->
  nth 0 (stern11 n) i.+1 = nth 0 (stern11 m) j.+1 ->
  i = j /\ n = m. 
Proof.
move => ha hb; move: (ltnW ha) (ltnW hb) => hc hd.
rewrite ! nth_stern11 // !addnS => sa sb.
suff sc: (2 ^ n + i) =  (2 ^ m + j).
   have he: 2^n +i < 2^n.+1 by rewrite expn2S -addnn ltn_add2l.
   have hf: 2^m +j < 2^m.+1 by rewrite expn2S -addnn ltn_add2l.
   case: (ltngtP n m).
   + rewrite - (leq_exp2l _ _ (ltnSn 1)) => xx.
     by move:(leq_trans he xx); rewrite sc ltnNge leq_addr.
   + rewrite - (leq_exp2l _ _ (ltnSn 1)) => xx.
     by move:(leq_trans hf xx); rewrite - sc ltnNge leq_addr.
   + by move => ea; move/eqP:sc; rewrite ea eqn_add2l => /eqP ->.
move: sa sb; move: (2 ^ n + i) (2 ^ m + j); clear => n m.
wlog : n m / n <= m.
   move => Hrec sa sb; case /orP:(leq_total n m) => sc; first by apply: Hrec.
   symmetry; apply: Hrec => //.
have aux a b c: b +a + c = a -> (b==0) && (c == 0).
  by rewrite (addnC b) -addnA -{2} (addn0 a) - addn_eq0 - (eqn_add2l a) => /eqP.
move:(stern_fusc)=> [Ha Hb Hc Hd].
move:(leqnn m); elim: m n {-2} m.
  by move => n m; rewrite leqn0 => /eqP ->; rewrite leqn0 => /eqP ->.
move => N Hrec n m; rewrite leq_eqVlt; case /orP; last first.
  by rewrite ltnS; apply: Hrec.
move/eqP => -> nN.
set u := n./2; set v := N.+1./2.
case: (odd_dichot n); case: (odd_dichot N.+1) => ea eb; 
  rewrite ea eb -/u -/v -? doubleS ?Hc ? Hd => sa sb.
+ move/eqP: sa; rewrite sb eqn_add2r => /eqP sa.
  have l1: u <= v by rewrite - leq_double -ltnS - eb - ea.
  have l2: v <= N by rewrite /v - leq_double - ltnS - ea double_le2.
  by rewrite (Hrec u v l2 l1 sa sb).
+ move: (esym sb); rewrite - sa => /aux /andP [_]. 
  by rewrite eqn0Ngt stern_gt0.
+ move: sb; rewrite  sa  => /aux /andP [_]. 
  by rewrite eqn0Ngt stern_gt0.
+ move/eqP: sb; rewrite sa eqn_add2l => /eqP sb.
  have l1: u <= v by rewrite - leq_double - eb - ea.
  have l2: v <= N.  
     rewrite /v - leq_double - ea; move:(f_equal odd ea); clear; case N=>//.
     move => n _ ; apply: double_le3.
  by rewrite (Hrec u v l2 l1 sa sb).
Qed.


Definition Stern_consecutive a b:= 
  exists n i, 
    [/\ i < 2^n, nth 0 (stern11 n) i = a  & nth 0 (stern11 n) i.+1 = b]. 

Lemma Stern_consecutive_coprime1 a b :
   Stern_consecutive a b -> coprime a b.
Proof. by move =>[n [i [ ha <- <-]]];  rewrite /coprime sternD_gcd_rec2. Qed.


Lemma Stern_consecutive_sym a b:
   Stern_consecutive a b -> Stern_consecutive b a.
Proof.
move => [n [i [pa pb pc]]].
have pe: 2 ^ n - i.+1 < 2 ^ n by rewrite - {2} (subnK pa) ltn_paddr.
have pf:(2 ^ n - i.+1).+1 < (2 ^ n).+1 by rewrite ltnS.
have pg:2 ^ n - i.+1 < (2 ^ n).+1 by apply: ltnW.
exists n, (2^n - i.+1). 
rewrite pe - stern11_symmetric! nth_rev size_sternD // subSS subKn // pc.
by rewrite - {1} (subnK pa) addnS - !addSn addKn pb.
Qed.

Lemma Stern_consecutive_nn a : Stern_consecutive a a -> a = 1.
Proof.
move => [n [i []]].
case:n => [| n lta]; first by rewrite ltnS leqn0 => /eqP -> /=.
have hb: i./2 < 2 ^ n.  
  rewrite -ltn_double -expn2S; exact: (leq_ltn_trans (double_half_le i) lta).
have hc:=(sternD_nth_compare_strict (ltnSn 0)(ltnSn 0) hb). 
case (odd_dichot i) => ea hd he; 
   move: hc; rewrite - ea hd he gtn_max ltnn ? andbF //.
Qed.


Lemma Stern_consecutive_rec a r n: Stern_consecutive a r ->
   Stern_consecutive a (n *a + r).
Proof. 
elim: n => // n H /H  [m [i [pa pb pc]]];rewrite mulSn - addnA.  
exists (m.+1), i.*2.
by rewrite sternD_nth_even sternD_nth_odd ? pa // pb pc expn2S ltn_double.
Qed.

Lemma Stern_consecutive_1n n: Stern_consecutive 1 n.+1.
Proof. 
have ha:Stern_consecutive 1 1 by exists 0,0.
by move:(Stern_consecutive_rec n ha); rewrite muln1 addn1.
Qed.

Lemma Stern_consecutive_coprime2 a b : 0 < a -> 0 < b -> coprime a b -> 
   Stern_consecutive a b.
Proof.
wlog: a b / a < b.
  move => h; case: (ltngtP a b) => ha hb hc hd.
  + by apply: h.
  + by apply:Stern_consecutive_sym; apply: h => //; rewrite coprime_sym.
  + by move: hd; rewrite /coprime - ha gcdnn => /eqP ->; exists 0,0. 
elim: b a {-2} b (leqnn b).
  move => a b; rewrite leqn0 => /eqP -> //.
move=> n H b a lan lab bp ap.
rewrite - coprime_modr coprime_sym => cp.
have ha: (a %% b < b) by rewrite ltn_mod bp.
move: (leq_trans lab lan); rewrite ltnS => hb.
case :(posnP (a %% b)) =>hc.
   move: cp;rewrite hc/coprime gcd0n => /eqP ->.
   rewrite -(prednK ap); apply: Stern_consecutive_1n.
rewrite (divn_eq a b); apply:Stern_consecutive_rec; apply:Stern_consecutive_sym.
exact: (H  (a %% b) b hb ha hc bp cp).
Qed.

Lemma sternD_location_bound b: 
   let H := fun k => exists i, b = nth 0 (stern11 k) i.*2.+1 in
   0 < b -> H b.-1 /\  forall k, H k -> k < b.
Proof.
move => H bp; split.
  exists 0 ; rewrite - {1} (prednK bp); elim (b.-1) => // m Ha.
  by rewrite sternD_nth_odd ?expn_gt0 // - Ha nth0 head_sternD add1n.
move => n [k kv].
case: (ltnP (k.*2)  (2 ^ n)) => ha.
   by rewrite kv; exact (sternD_nth_compare_rec (leqnn 1) (leqnn 1) ha).
by move: (ltn_eqF bp); rewrite kv nth_default // size_sternD ltnS ha.
Qed.




Lemma fusc_totient b: 0 < b ->
  \sum_(i< 2^ b.-1) (b== fusc (i.*2.+1)) = totient b.
Proof.
set m := 2^ b.-1 => bp.
move:(prednK bp); set b' := b.-1; move => sa.
have Ha: forall i, fusc i < fusc (i.*2.+1).
  by move => i; rewrite fusc_odd ltn_paddr // fusc_gt0.
pose f (i: 'I_m) := inord (fusc i): 'I_(b'.+1). 
set D := [pred i:'I_m  |b == fusc i.*2.+1].
have: {in D &, injective f}.
   move => u v; rewrite ! inE => /eqP ea /eqP eb sb.
   have hu: fusc u < b'.+1 by rewrite sa ea; apply: Ha.
   have hv: fusc v < b'.+1 by rewrite sa eb; apply: Ha.
   apply:ord_inj;apply/eqP; rewrite - eqn_double. 
   apply/eqP/fuscp_injective; last by rewrite - ea - eb.
   by rewrite !fusc_even - (inordK hu) - (inordK hv) -/(f u) -/(f v) sb.
move/card_in_imset; rewrite - (sum1_card D) big_mkcond /= => <-.
have <-: #|[set i:'I_(b'.+1) | coprime b i]| = totient b.
  rewrite totient_count_coprime big_mkord - sum1_card big_mkcond sa //=.
  by apply: congr_big => // i _ /=; rewrite inE.
apply: eq_card => a; rewrite inE;  apply/imsetP/idP.
  move => [i]; rewrite inE => /eqP ea eb.
  have hu: fusc i < b'.+1 by rewrite sa ea; apply: Ha.
  by rewrite ea eb /f (inordK hu) - (fusc_even i) coprime_sym fusc_coprime.
move => ce;move:(ltn_ord a); rewrite {2} sa => lab.
move: (subnK (ltnW lab)); set c := _ - _; rewrite addnC => ea.
have cap: coprime a c by move: ce; rewrite - ea /coprime gcdnC gcdnDl.
move:lab; rewrite - subn_gt0; rewrite -/c => cp.
rewrite - (prednK cp) in cap.
move: (fusc_pair_surj cap) => [n [ha hb]].
have bn: b = fusc (n.*2.+1) by rewrite -ea ha - (prednK cp) hb fusc_odd.
have lnm: n < m.  
  rewrite /m bn -ltn_double -expn2S prednK ?fusc_gt0 //.
  apply: fusc_lower_bound. 
exists (Ordinal lnm); rewrite ? inE ? bn // /f - ha inord_val //.
Qed.

Lemma fusc_totient2 n b: 0 < b -> b <= n.+1 ->
  \sum_(2^n <= i< 2^(n.+1)) (b== fusc i) = totient b.
Proof.
set m := 2^ n.+1.
move => sa sb; rewrite -(fusc_totient sa).
move:(prednK sa); set b' := b.-1; move => sac.
have sc: 2 ^ b' <= 2 ^ n by rewrite leq_exp2l  // -ltnS sac.
pose g i := (i.*2.+1) * 2 ^(n.+1 - log2 (i.*2.+1)).
have Hb: forall i,  b = fusc i.*2.+1 -> b = fusc (g i).
  by move => i ->; rewrite /g  mulnC fusc_kpow2n.
have Ha: forall i, i < 2 ^ b' -> 2^n <= g i < m.
  move => i ha;move/andP:(log2_bnd i.*2) => [hb hc].
  set j := i.*2.+1.
  have hb': 2 ^ log2 j <= j.*2 by rewrite log2S_k expn2S leq_double.
  have hd: log2 j <= n.+1. 
    apply: leq_trans sb; rewrite - ltnS  -(ltn_exp2l _ _ (ltnSn 1)).  
    apply: (leq_ltn_trans  hb'); rewrite expn2S ltn_double /j - sac.
    by rewrite - doubleS expn2S leq_double.
  rewrite /g /m  - leq_double - expn2S - {1 4} (subnKC hd) expnD ltn_mul2r.
  rewrite expn_gt0 hc /= - mul2n mulnA mul2n leq_pmul2r ? hb' ? expn_gt0 //.
pose M := 2^b'.
have mp: 0 < m by rewrite /m expn_gt0.
move:(prednK mp); set m' := m.-1 => mpp.
pose f (i: 'I_M) := inord (g i): 'I_m'.+1. 
set D := [pred i:'I_M  |b == fusc i.*2.+1].
have Hc: forall u: 'I_M, (@nat_of_ord m'.+1 (inord (g u))) = g u. 
  by move => u; move /andP: (Ha _ (ltn_ord u)) => [_]; rewrite -mpp => /inordK.
have: {in D &, injective f}.
   move => u v; rewrite ! inE /f => /eqP ea /eqP eb ec; apply: ord_inj.
   move: (f_equal (@nat_of_ord m'.+1) ec). 
   by rewrite (Hc u) (Hc v) /g; move/elogn2_unique.
move/card_in_imset; rewrite - (sum1_card D) big_mkcond /= => <-.
set x := LHS. 
have: x = #|[set i:'I_m'.+1 | (2^n <= i) && (b == fusc i) ]|.
  rewrite - sum1dep_card big_mkcondr /=.
  rewrite - (big_mkord _ (fun i => if (b == fusc i) then 1 else 0)).
  have qa: 0 <= 2^n by [].
  have qb: 2^n <= m'.+1 by rewrite mpp /m expn2S double_le1.
  rewrite (big_cat_nat _ _ _ qa qb) /= big1_seq.
    by rewrite add0n big_mkcond /= /x mpp; apply: eq_big_nat => i /andP[->].
  by move => i; rewrite mem_iota add0n subn0 ltnNge => /and3P [->] //.
move => ->; clear x; apply: eq_card => a; rewrite inE;  apply/idP/imsetP.
  move => /andP [pa pb]; rewrite /f.
  case: (posnP a) => az; first by move: sa; rewrite (eqP pb) az fusc0.
  case: (elogn2P a.-1) => e q; rewrite (prednK az) => aq.
  have fq: fusc (q.*2.+1) = b by rewrite (eqP pb) aq fusc_kpow2n.
  move: (fusc_lower_bound q); rewrite fq - sac expn2S ltn_double => qm.
  have: 2^n <= a < 2^n.+1 by rewrite pa -/m - mpp (ltn_ord a).
  move/log2_pr; rewrite aq mulnC log2_mul_exp // => aa.
  exists (Ordinal qm); first by rewrite inE fq.
  by apply:ord_inj;rewrite Hc /= /g - aa addnK mulnC.
move => [x]; rewrite inE /f => qa qb.
move:(Ha _ (ltn_ord x)) => /andP[ra rb]; rewrite qb inordK ? mpp // ra /=.
by apply /eqP /Hb /eqP.
Qed.

Lemma fusc_totient_prime b
  (H := fun b =>  \sum_(2^(b.-1) <= i< 2^ b) (b== fusc i) = b .-1) :
  (prime b -> H b) /\ (0 < b -> H b  -> prime b).
Proof.
split.
  move => h. 
  have bp:= (prime_gt0 h).
  move: (leqnn b); rewrite - {2} (prednK bp) => h2.
  move:(fusc_totient2 bp h2); rewrite  (prednK bp).
    by rewrite (totient_pfactor h (ltn0Sn 0)) muln1.
move => bp; move: (leqnn b); rewrite - {2} (prednK bp) totient_prime bp => h2.
by move:(fusc_totient2 bp h2); rewrite /H  (prednK bp) => -> ->; rewrite eqxx.
Qed.


Lemma sternD_bezout n i (f := fun n i => nth 0 (stern11 n) i):
    i < 2 ^n -> (f n i) * (f n.+1 i.+1) = 1 +  (f n i.+1) * (f n.+1 i).
Proof.
move => h; move: (ltnW h) => h1.
have h2: i < 2 ^ n.+1 by rewrite  expn2S -addnn; apply:ltn_addr.
move: (ltnW h2) => h3.
rewrite /f !nth_stern11 // !sternD_fusc ! fusc_col_progression //.
by rewrite ! mulnDr mulnC addnCA fusc_bezout2.
Qed.


Lemma fusc_bezout_minimal n i 
    (a := fusc (2 ^ n + i))(b:= fusc (2 ^ n + i.+1)): 
   i < 2 ^n ->
   fusc i.+1 * a = fusc i * b + 1
   /\ (forall u v, u* a = v * b +1 -> (fusc i.+1 <= u) && (fusc i <= v)).
Proof.
move => H.
move: (fusc_bezout2 H); rewrite -/a -/b addnC mulnC (mulnC b) => eq1.
have ha: fusc i < a by rewrite(ltn_leqif  (fusc_bound (ltnW H))) (ltn_eqF H).
split => // u v eq2. 
exact:(minimal_bezout_prop eq1 ha (fusc_bound H) eq2).
Qed.


Lemma sternD_1n_kl n q i: i <= 2^q ->
   nth 0 (sternD 1 n q) i = stern (2 ^ q - i) + n * stern i.
Proof. by move => h; rewrite sternD_stern // mul1n. Qed.


Lemma sternD_1n_kl_sym n q i j (k :=  stern j) (l := stern i):
  i + j = 2^q ->  nth 0 (sternD 1 n q) i = k + n * l /\ coprime k l.
Proof.
rewrite /k/l => sb.
have sc: i <= 2 ^q by rewrite -sb leq_addr.
by rewrite sternD_1n_kl// -sb addKn !sternD_fusc coprime_sym (fusc_fusc3 sb).
Qed.

Lemma sternD_1n_v n q i:
  i <= 2^q -> nth 0 (sternD 1 n.+1 q) i = nth 0 (stern11 (q + n)) i. 
Proof.
elim: n q i; first by move => k i h;rewrite addn0.
move => n Hrec k i la.
rewrite - (add1n n.+1) -split_sternD_left nth_take ? ltnS // - addSnnS Hrec //.
by rewrite  expn2S -addnn (leq_trans la) // leq_addl.
Qed.


Lemma sternD_1n_v' n q i:
  i <= 2^q -> nth 0 (sternD 1 n.+1 q) i = stern (2^ (q + n) + i). 
Proof. 
move => h; rewrite sternD_1n_v // nth_stern11 //; apply: (leq_trans h).
by rewrite expnD; apply: leq_pmulr; rewrite expn_gt0.
Qed.

Lemma sternD_1n_small n (S := sternD 1 n.+2)
   (C := fun a b => exists i k, 
    [/\ i < 2^k, a = nth 0 (S k) i & b = nth 0 (S k) i.+1]) a b:
  C a b -> C b a -> False.
Proof.
move => [i [k [pa pb pc]]] [j [l [qa qb qc]]].
move: pb pc; rewrite (sternD_1n_v _ (ltnW pa)) (sternD_1n_v n.+1 pa).
move: qb qc; rewrite (sternD_1n_v _ (ltnW qa)) (sternD_1n_v n.+1 qa).
have pd: i < 2 ^ (k + n.+1). 
  by rewrite expnD; apply: (leq_trans pa) ;rewrite leq_pmulr // expn_gt0.
have qd: j < 2 ^ (l + n.+1). 
  by rewrite expnD; apply: (leq_trans qa) ;rewrite leq_pmulr // expn_gt0.
move:(ltnW pd)(ltnW qd) => pd' qd'.
rewrite !nth_stern11 // (addnS _ j) (addnS _ i) !sternD_fusc.
set x := 2 ^ (k + n.+1) + i; set y := 2 ^ (l + n.+1) + j.
move => qb qc pb pc.
set p := 2 ^ (k + n.+1).
have la : p <= x by rewrite /p/x leq_addr /=.
have lb : x < p.*2 by rewrite /p/x - addnn ltn_add2l.
have lc: p <= x <= p.*2 by rewrite la (ltnW lb).
have ld:  p <= x.+1 <= p.*2 by rewrite lb andbT ltnW.
pose x' := 3 * p - x.+1.
have ea: x.+1 + x' = 3 *p.
   apply: subnKC. apply: (leq_trans lb); rewrite -mul2n. 
   by apply: leq_pmul2r; rewrite expn_gt0.
have eb: x + x'.+1 = 3 *p by rewrite - addSnnS ea.
have ly:log2 y = (l + n.+1).+1.
   by apply: log2_pr; rewrite expn2S - addnn ltn_add2l leq_addr qd.
have lx:log2 x' = (k + n.+1).+1.
   apply: log2_pr; rewrite expn2S -/p - (leq_add2l p.*2) -(ltn_add2l p) addnC.
   by rewrite -mul2n -mulSn - ea leq_add2r ltn_add2r mul2n lb ltnS la.
move:(fusc_palindrome lc eb) (fusc_palindrome ld ea).
rewrite - pb - pc qc qb => sa sb.
move: (fuscp_injective sb sa) => ec.
have kl: l = k by apply/eqP; rewrite -(eqn_add2r n.+1) - eqSS -lx - ly ec.
have ha: y < 2 ^ (k + n.+1) + 2 ^k by rewrite -kl /y ltn_add2l.
have hb: 2 ^ k <= (2 ^ (k + n.+1)).*2. 
  by rewrite -expn2S leq_exp2l // - addnS leq_addr.
have hc:2 ^ (k + n.+1) + 2 ^ k <= (2 ^ (k + n.+1)).*2 - 2 ^ k.
   rewrite -(leq_add2l (2^k)) subnKC // addnCA -addnn  addnn leq_add2l. 
   by rewrite - expn2S -addSnnS leq_exp2l // leq_addr //.
have hd:  (2 ^ (k + n.+1)).*2 - 2 ^ k <= x'.
  rewrite - (leq_add2r (2^k)) (subnK hb) - (leq_add2l x.+1) addnA ea.
  by rewrite -/p mulSn mul2n addnAC leq_add2r /x ltn_add2l.
by move: (leq_trans ha (leq_trans hc hd)); rewrite ec ltnn.
Qed.

Lemma sternD_1n_member a n:
  (exists k i, i <=2^k /\ a =  nth 0 (sternD 1 n k) i) <->
  (a==1 \/ n <= a).
Proof.
split.
  move => [k [i [pa ->]]]; rewrite sternD_1n_kl // !sternD_fusc.
  case iz: (i==0); first by left; rewrite (eqP iz) subn0 fusc_pow2 muln0 addn0.
  have h: n <= n * fusc i by rewrite leq_pmulr // fusc_gt0 lt0n iz.
  by right; rewrite (leq_trans h) // leq_addl. 
case => ap; first by rewrite (eqP ap);exists 0, 0.
have ha: 0 < 2 ^ (a - n) by  rewrite expn_gt0.
exists (a-n), 1; split => //; rewrite sternD_1n_kl // muln1 subn1.
by rewrite sternD_fusc fusc_pred_pow2 subnK.
Qed.


Lemma sternD_1n_H1 q n i: i <= 2^q ->
   nth 0 (sternD 1 n q.+1) i = nth 0 (stern11 q) i + n * nth 0 (stern01 q) i.
Proof.
move => h.
have h': i <= 2 ^ q.+1 by rewrite expn2S - addnn (leq_trans h) //leq_addr.
by rewrite sternD_1n_kl // stern_prop // nth_stern11_sym.
Qed.


Lemma sternD_1n_H2 q n i: i <= 2^ q ->
   nth 0 (sternD 1 n q.+1) (i + 2^q) = 
   nth 0 (sternD 1 0 q) i + n * nth 0 (stern11 q) i.
Proof.
move => ha.
have hb: i + 2 ^ q <= 2 ^ q.+1 by rewrite expn2S -addnn leq_add2r.
rewrite  sternD_1n_kl// expn2S -addnn nth_stern11 // (addnC i); congr addn.
by rewrite  sternD_1n_kl // mul0n addn0 subnDl.
Qed.

Lemma sternD_1n_H2' q n i: i <= 2^ q ->
   nth 0 (sternD 1 n q.+1) (2^q.+1 - i) = 
   nth 0 (stern01 q) i + n * nth 0 (stern11 q) i.
Proof.
move => ha.
have hb: i <= 2 ^ q.+1 by rewrite expn2S- addnn (leq_trans ha) // leq_addr.
rewrite sternD_rev nth_rev size_sternD ? ltnS ? leq_subr //.
rewrite subnS subSKn subKn // sternD_stern // mul1n stern_prop //.
by rewrite nth_stern11_sym ? leq_subr // expn2S -addnn addnC.
Qed.

Lemma sternD_1n_disymmetric n q i j (S := sternD 1 n.+2 q) :
   i < j -> i + j = 2^q -> nth 0 S i < nth 0 S j.
Proof.
move => sa sb.
have: i.*2 < 2^q by rewrite - sb - addnn ltn_add2l.
rewrite /S; clear S; move: sa sb;case: q.
  rewrite expn0 ltnS (leq_double i 0) leqn0; move => sb sd sc; move: sd.
  rewrite (eqP sc) add0n => -> //.
move => q sa sb; rewrite expn2S ltn_double => sc.
have ->: j =  2 ^ q.+1 - i by rewrite - sb addKn.
have h := ltnW sc.
rewrite (sternD_1n_H1 _ h) (sternD_1n_H2' _ h).
rewrite mulSn addnCA (mulSn n.+1) ltn_add2l ltn_add2l ltn_pmul2l //.
rewrite (stern_prop h) (sternD_stern _ _ h) !mul1n.
by rewrite ltn_paddl // stern_gt0 // subn_gt0.
Qed.


Lemma sternD_1n_bezout n q i (S := sternD 1 n q) 
  (k:= stern (2 ^ q - i)) (l:= stern i)
  (k':=  stern (2 ^ q - i.+1)) (l':= stern i.+1):
  i < 2^q ->
  [/\ nth 0 S i = k + n*l, nth 0 S i.+1 = k' + n*l' &  k * l' = k' * l + 1 ].
Proof.
rewrite (mulnC k) (mulnC k') /S/k/k'/l/l'; clear. 
case:q. 
  have s0: stern 0 = 0 by [].
  have s1: stern 1 = 1 by [].
  by rewrite ltnS leqn0 => /eqP -> //=; rewrite s0 s1 muln0 muln1.
have HA: forall i q, i < 2^q -> stern i.+1 * stern (2 ^ q.+1 - i)  =
      stern i * stern (2 ^ q.+1 - i.+1) + 1.
   move => j q liq; move:  (ltnW liq) => liq'.
   move:(proj1 (fusc_bezout_minimal liq)).
   rewrite -!sternD_fusc - !nth_stern11 // !nth_stern11_sym //.
move => q liq.
rewrite (sternD_1n_kl _ (ltnW liq)) (sternD_1n_kl _ liq); split => //.
case (ltnP i (2^q)) => ha; first by apply: HA.
set j := 2^ q.+1 - i.+1.
have hc: (2 ^ q.+1 - j) = i.+1 by rewrite- (subnK liq) -/j addKn.
have hd: (2 ^ q.+1 - j.+1) = i by rewrite subnS hc.
have j': (2 ^ q.+1 - i) = j.+1 by rewrite -(subnK liq) -/j -addSnnS addnK.
have ljq: j < 2^q.  
  by rewrite -(leq_add2r i) /j addSnnS subnK // expn2S -addnn leq_add2l.
rewrite j' (mulnC _ (stern j.+1)) (mulnC _ (stern j)).  
by move: (HA j q ljq); rewrite hc hd.
Qed.



Lemma sternD_1n_coprime n q i: i < 2^q -> exists K L,
  coprime K L /\ nth 0 (sternD 1 n q) i = K + n*L.
Proof.
move => h; move: (sternD_1n_bezout n h) => [-> _]. 
rewrite mulnC => /coprime_if_bezout.
by exists (stern (2 ^ q - i)), (stern i). 
Qed.


Lemma sternD_1n_coprime_rev n K L: coprime K L ->
  exists i q, [/\ i < 2^q, odd i & nth 0 (sternD 1 n q) i = K + n*L].
Proof.
move => cp. admit.
Abort.


(* ----- *)
End Stern.





