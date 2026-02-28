(*
    Copyright (C) 2012  G. Gonthier, B. Ziliani, A. Nanevski, D. Dreyer

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

HB.mixin Record isTotalOrder T & Equality T := {
  ord : rel T;
  irr : irreflexive ord;
  trans : transitive ord;
  total : forall x y, [|| ord x y, x == y | ord y x];
}.

#[short(type="ordType")]
HB.structure Definition Order := { T of Equality T & isTotalOrder T }.

Arguments ord {s}.
Arguments irr {s}.
Arguments trans {s} [y x z].

(* Prenex Implicits ord. *)

Section Lemmas.
Variable T : ordType.

Lemma nsym (x y : T) : ord x y -> ord y x -> False.
Proof. by move=>E1 E2; move: (trans E1 E2); rewrite irr. Qed.

End Lemmas.

Section Totality.
Variable K : ordType.

CoInductive total_spec (x y : K) : bool -> bool -> bool -> Type :=
| total_spec_lt of ord x y : total_spec x y true false false
| total_spec_eq of x == y : total_spec x y false true false
| total_spec_gt of ord y x : total_spec x y false false true.

Lemma totalP x y : total_spec x y (ord x y) (x == y) (ord y x).
Proof.
case H1: (x == y).
- by rewrite (eqP H1) irr; apply: total_spec_eq.
case H2: (ord x y); case H3: (ord y x).
- by case: (nsym H2 H3).
- by apply: total_spec_lt H2.
- by apply: total_spec_gt H3.
by move: (total x y); rewrite H1 H2 H3.
Qed.
End Totality.

Section NatOrd.
Lemma irr_ltn_nat : irreflexive ltn. Proof. by move=>x; rewrite /= ltnn. Qed.
Lemma trans_ltn_nat : transitive ltn. Proof. by apply: ltn_trans. Qed.
Lemma total_ltn_nat : forall x y, [|| x < y, x == y | y < x].
Proof. by move=>*; case: ltngtP. Qed.
HB.instance Definition _ :=
  isTotalOrder.Build nat irr_ltn_nat trans_ltn_nat total_ltn_nat.
End NatOrd.

Section ProdOrd.
Variables K T : ordType.

(* lexicographic ordering *)
Definition lex : rel (K * T) :=
  fun x y => if x.1 == y.1 then ord x.2 y.2 else ord x.1 y.1.

Lemma irr_lex : irreflexive lex.
Proof. by move=>x; rewrite /lex eq_refl irr. Qed.

Lemma trans_lex : transitive lex.
Proof.
move=>[x1 x2][y1 y2][z1 z2]; rewrite /lex /=.
case: ifP=>H1; first by rewrite (eqP H1); case: eqP=>// _; apply: trans.
case: ifP=>H2; first by rewrite (eqP H2) in H1 *; rewrite H1.
case: ifP=>H3; last by apply: trans.
by rewrite (eqP H3)=>R1; move/(nsym R1).
Qed.

Lemma total_lex : forall x y, [|| lex x y, x == y | lex y x].
Proof.
move=>[x1 x2][y1 y2]; rewrite /lex /=.
case: ifP=>H1.
- rewrite (eqP H1) eq_refl -pair_eqE /= eq_refl /=; exact: total.
rewrite (eq_sym y1) -pair_eqE /= H1 /=.
by move: (total x1 y1); rewrite H1.
Qed.

HB.instance Definition _ :=
  isTotalOrder.Build (K * T)%type irr_lex trans_lex total_lex.
End ProdOrd.

Section FinTypeOrd.

Definition fin_order (T : Type) := T.

HB.instance Definition _ (T : eqType) := Equality.copy (fin_order T) T.

Variable T : finType.

Definition ordf : rel T :=
  fun x y => index x (enum T) < index y (enum T).

Lemma irr_ordf : irreflexive ordf.
Proof. by move=>x; rewrite /ordf ltnn. Qed.

Lemma trans_ordf : transitive ordf.
Proof. by move=>x y z; rewrite /ordf; apply: ltn_trans. Qed.

Lemma total_ordf : forall x y, [|| ordf x y, x == y | ordf y x].
Proof.
move=>x y; rewrite /ordf; case: ltngtP=>//= H; rewrite ?orbT ?orbF //.
have [H1 H2]: x \in enum T /\ y \in enum T by rewrite !mem_enum.
by rewrite -(nth_index x H1) -(nth_index x H2) H eq_refl.
Qed.

HB.instance Definition _ :=
  isTotalOrder.Build (fin_order T) irr_ordf trans_ordf total_ordf.

End FinTypeOrd.

HB.instance Definition _ (n : nat) := Order.copy 'I_n (fin_order 'I_n).
