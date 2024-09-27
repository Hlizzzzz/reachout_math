Require Import List Arith Classical ClassicalEpsilon Lia.

Section FiniteSetOperation.

Definition finite [T : Type] (s : T -> Prop) := 
  exists l : list T, forall x, s x -> In x l.

Definition singleton [T : Type](x:T) :=
  fun y => y=x.

Definition union[T : Type] (s1 s2:T -> Prop) :=
    fun x => s1 x \/ s2 x.

Definition intersection [T : Type] (s1:T -> Prop)(s2:T -> Prop) :=
    fun x => s1 x /\ s2 x.

Definition compl [T : Type] (s : T -> Prop)(x : T) :=
  not(s x).

Lemma union_comm [T : Type] (s1 s2:T -> Prop):
forall x:T ,(union s1 s2) x  <->(union s2 s1)x .
Proof.
intros x.
apply (or_comm (s1 x) (s2 x)) .
Qed.

Lemma intersection_comm[T : Type] ( s1 s2 : T -> Prop) :
forall x : T, (intersection s1 s2) x <-> (intersection s2 s1) x.
Proof.
unfold intersection.
intros x.
apply (and_comm (s1 x)(s2 x)).
Qed.

Lemma finite_0 [T : Type] (s0 : T -> Prop) :
  (forall x, ~s0 x) -> finite s0.
Proof.
now intros char_empty; exists nil; intros x xinempty; case (char_empty x).
Qed.

Lemma finite_singleton [T: Type](a : T) :
  finite (singleton a).
Proof.
unfold singleton.
unfold finite.
exists (a::nil); intros x H.
simpl; auto.
Qed.
  
Lemma Union_preserves_Finite [T : Type](s1 : T -> Prop)(s2 : T -> Prop):
(finite s1 /\ finite s2)  <-> finite (union s1 s2).  
Proof.
split.
  intros [f1 f2].
  unfold finite in *.
  destruct f1 as [LIh1 H1].
  destruct f2 as [LIh2 H2].
    exists (LIh1++LIh2).
    intros x H'.
      destruct H'.
    apply (in_or_app LIh1 LIh2 x) ;left ;apply H1;exact H.
  apply (in_or_app LIh1 LIh2 x) ;right ;apply H2;exact H.
intros [L Ih].
  unfold finite in *.
    split;exists L; intros x H; apply Ih.
  left; exact H.
right; exact H.
Qed.

Lemma Intersection_preserves_Finite [T : Type](s1 s2 : T -> Prop):
(finite s1 \/ finite s2)  -> finite (intersection s1 s2).
Proof.
intros.
unfold finite in *.
destruct H.
destruct H as [L1 Ih1];exists L1;intros x [H1 H2];apply Ih1;exact H1.
destruct H as [L2 Ih2];exists L2;intros x [H1 H2];apply Ih2;exact H2.
Qed.

Lemma Subset_Finite [T : Type] (s s' : T -> Prop) :
 (forall x, s' x -> s x) ->( finite s -> finite s') .
Proof.
intros Hsubset Hf.
unfold finite in *.
destruct Hf as [L Ih].
exists L.
intros.
apply Ih.
apply Hsubset.
exact H.
Qed.

End FiniteSetOperation.

Section Cardinal.

Definition Pcard [T : Type] (s : T -> Prop) (n : nat) :=
 (exists l, (forall x, s x -> In x l) /\ n = length l) /\
 (forall l, (forall x, s x -> In x l) -> n <= length l).

Definition card [T : Type] (s : T -> Prop) :=
  (epsilon (inhabits 0) (Pcard s)).

Lemma card_def: forall [T : Type] (s : T -> Prop),
  (exists n, Pcard s n) -> Pcard s (card s).
Proof.
intros T s.
apply epsilon_spec.
Qed.

Lemma card_0[T: Type]: forall s: T-> Prop, ( forall x ,~s x)-> card s = 0.
Proof.
intros s sempty.
assert (cards0 : Pcard s 0).
  split.
    exists nil.
    split.
      now intros x sx; case (sempty x).
    easy.
  intros l _; apply Nat.le_0_l.
destruct (card_def _ (ex_intro _ 0 cards0)) as [_ min].
enough (cle0 : card s <= 0) by now apply eq_sym; apply le_n_0_eq.
now change 0 with (length (@nil T)); apply min; intros x sx; case (sempty x).
Qed.

Inductive elem_removed [T : Type] (x : T) : list T -> list T -> Prop :=
  remove_one : forall l, elem_removed x l (x :: l)
| remove_extra : forall y l1 l2, 
   elem_removed x l1 l2 ->
   elem_removed x (y :: l1) (y :: l2).

Lemma remove_elem [T : Type] (x : T) (l : list T) :
  In x l -> exists l1, elem_removed x l1 l.
Proof.
induction l as [ | y l' Ih].
  easy.
simpl; intros [yisx | yinl'].
  exists l'; rewrite yisx; apply remove_one.
destruct (Ih yinl') as [l2 Pl2].
now exists (y :: l2); apply remove_extra.
Qed.

Lemma remove_length [T : Type] (x : T) (l1 l2 : list T) :
  elem_removed x l1 l2 -> length l2 = S (length l1).
Proof.
induction 1 as [ | a l1 l2 erl1l2 Ih];[easy | ].
now simpl; rewrite Ih.
Qed.

Lemma elem_removed_in [T : Type] (x : T) (l1 l2 : list T) (y : T) :
  elem_removed x l1 l2 ->
  In y l2 -> y = x \/ In y l1.
Proof.
induction 1 as [ | a l1 l2 erl1l2 Ih].
  simpl; intros [yisx | yinl1];[now left; rewrite yisx | now right].
simpl; intros [aisy | ainl2].
  now right; left.
destruct (Ih ainl2) as [yisx | yinl1].
  now left.
now right; right.
Qed.

Lemma card_s[T: Type]: forall s: T-> Prop, forall n, forall x : T,
  Pcard s n ->
  ~s x -> Pcard (fun y => y = x \/ s y) (S n).
Proof.
intros s n x cardsn xout.
destruct cardsn as [[wl [wlin wls]] minc].
split.
  exists (x :: wl); split.
    now intros y [yisx | sy]; simpl;[left | right]; auto.
  now simpl; rewrite <-wls.
intros l lcovers.
assert (xinl : In x l).
  now apply lcovers; left.
destruct (remove_elem x l xinl) as [l' Pl'].
rewrite (remove_length _ _ _ Pl').
apply le_n_S.
apply minc.
intros y sy.
assert (yl : In y l).
  now apply lcovers; right.
destruct (elem_removed_in _ l' _ y Pl' yl) as [yisx | yinl'];[ | easy].
case xout.
now rewrite <- yisx.
Qed.

Lemma finite_Pcard [T : Type] (s : T -> Prop) :
  finite s -> exists n, Pcard s n.
Proof.
intros [l Pl]; revert s Pl.
induction l as [ | a l' Ih].
  intros s empty.
    exists 0.
  split.
    exists nil; split;[ | easy].
    assumption.
  now intros l _; apply le_0_n.
simpl.
intros s ssub.
pose (s' := fun x => s x /\ x <> a).
assert (s'sub : forall x, s' x -> In x l').
  intros x s'x.
  assert (sx : s x) by now destruct s'x.
  destruct (ssub _ sx) as [aisx | xinl]; auto.
  now rewrite <- aisx in s'x; destruct s'x as [_ abs]; case abs.
destruct (Ih s' s'sub) as [n' [[wl [s'subw n'w]] min']].
case (classic (s a)) as [sa | ans].
  exists (S n').
  split.
    exists (a :: wl).
    split.
      intros x sx.
      case (classic (x = a)) as [xisa | xna].
        now simpl; rewrite xisa; auto.
      simpl; right.
      apply s'subw.
      now split; auto.
    now simpl; rewrite n'w.
  intros l ssubl.
  assert (exists l2,  elem_removed a l2 l) as [l2 Pl2].
    apply remove_elem.
    apply ssubl.
    exact sa.
  assert (Pl2' := Pl2).
  apply remove_length in Pl2.
  assert (minl2 : n' <= length l2).
    apply min'.
    intros x [sx xna].
    apply (elem_removed_in _ _ _ x) in Pl2'.
      destruct Pl2' as [xisa | xinl2].
        now case xna.
      easy.
    now apply ssubl; apply sx.
  lia.
exists n'.
assert (ss' : forall x, s x -> s' x).
  intros x sx; split;[easy | ].
  now intros xisa; rewrite xisa in sx; case ans.
split.
  exists wl.
  split;[ | easy].
  intros x sx; apply s'subw.
  now apply ss'.
intros l ssubl.
apply min'.
intros x s'x; apply ssubl.
now destruct s'x.
Qed.

Lemma Pcard_card [T : Type](s : T -> Prop):
forall n, Pcard s n -> card s = n.
Proof.
intros n pcards.
destruct pcards as [[L H] H'].
destruct H as [Ih len].
assert (fs : finite s ).
exists L; auto.
assert (card_tmp := finite_Pcard s fs ).
assert (tmp := card_def _ card_tmp).
destruct tmp as [[L' [tmpH1 tmpH1']] tmpH2].
apply tmpH2 in Ih.
apply H' in tmpH1.
lia.
Qed.

End Cardinal.

Section Enumeration.

(* When does a list enumerate all elements of a finite set. *)

Definition Penum [T : Type] (s : T -> Prop) (l : list T) :=
 (forall x, s x -> In x l) /\
 (forall l',  (forall x, s x -> In x l') -> length l <= length l').

Definition enum [T : Type] (s : T -> Prop) :=
  (epsilon (inhabits nil) (Penum s)).

Lemma enum_def: forall [T : Type](s : T-> Prop),
(exists l:list T, Penum s l) -> Penum s (enum s). 
Proof.
intros T s.
apply epsilon_spec.
Qed.

Lemma finite_has_minimal_list [T : Type] (s : T -> Prop) :
  finite s <-> exists l, Penum s l.
Proof.
assert (right_to_left : (exists l, (forall x, s x -> In x l) /\ 
                (forall l',  (forall x, s x -> In x l') -> 
                    length l <= length l')) -> finite s).
  intros [l Pl].
  destruct Pl as [Pl1 _].
  exists l; exact Pl1.
split;[ | auto].
clear right_to_left.
intros fs.
assert (tmp := finite_Pcard s fs).
unfold Pcard in tmp.
destruct tmp as [n [Htmp1 Htmp2]].
destruct Htmp1 as [L H1].
exists L.
destruct H1 as [fL nth].
unfold Penum.
rewrite <-nth.
auto.
Qed.

Lemma enum_card [T : Type] (s : T -> Prop) (l : list T):
  Penum s l -> card s = length l.
Proof.
intros en.
assert (fs : finite s).
  now exists l; destruct en as [it _].
assert (card_tmp := finite_Pcard s fs).
assert (tmp := card_def _ card_tmp); clear card_tmp.
destruct tmp as [tmpH1 tmpH2].
destruct en as [tmpH1' tmpH2'].
apply tmpH2 in tmpH1'.
destruct tmpH1 as [l' [Pl' cardv]].
apply tmpH2' in Pl'.
rewrite <- cardv in Pl'.
lia.
Qed.

Lemma finite_enum_card [T : Type] (s : T -> Prop) :
  finite s -> card s = length (enum s).
Proof.
intros fs.
apply enum_card.
apply enum_def.
now rewrite <- finite_has_minimal_list.
Qed.

Lemma Penum_finite[T : Type](s : T -> Prop)(l : list T):
Penum s l -> finite s.
Proof.
intros ensl; exists l.
destruct ensl as [H H0].
exact H.
Qed.

Lemma Penum_included [T : Type] (s : T -> Prop) (l : list T) :
  Penum s l -> forall x, In x l -> s x.
Proof.
intros Ph x H.
destruct Ph as [fsH H1].
assert(fs : finite s).
now apply (Penum_finite s l).
rewrite (finite_has_minimal_list s ) in fs.
assert (tmp' := enum_def _ fs).
destruct tmp' as [tmpH1' tmpH2'].
assert (eqle:length l = length (enum s) ).
now apply H1 in tmpH1';apply tmpH2' in fsH;lia.
destruct (remove_elem x l H) as [l1 Pl1].
case (classic (s x)); auto.
intros nsx.
assert (sincludedl1 : forall y: T , s y -> In y l1).
intros y sy.
assert (tmp := elem_removed_in x l1 l y Pl1 (fsH y sy)).
destruct tmp as [yx | It ]; auto.
case ( nsx ).
rewrite <- yx ;auto.
apply tmpH2' in sincludedl1.
assert (tmpl := remove_length x l1 l Pl1).
rewrite eqle in tmpl.
lia.
Qed.

Lemma finite_enum_included [T : Type](s : T -> Prop):
  finite s -> (forall x, In x (enum s) -> s x).
Proof.
intros fs x H.
rewrite (finite_has_minimal_list s ) in fs.
apply (Penum_included s (enum s)).
apply enum_def;auto.
auto.
Qed.

End Enumeration.

Section FiniteSetFacts.

Lemma card_not_0_has_elem [T : Type](s : T -> Prop):
finite s -> card s <> 0 -> exists a : T , s a.
Proof.
intros fs H.
assert(th := finite_enum_card s fs).
assert (Hfei := finite_enum_included s fs).
destruct (enum s ) as [| a tl].
rewrite th in H.
easy.
exists a.
apply Hfei.
simpl.
left.
easy.
Qed.

Lemma Penum_add_elem [T : Type] (s : T -> Prop) (a : T) (l : list T):
  Penum s l -> ~ s a -> Penum (union (singleton a) s) (a :: l).
Proof.
intros en nsa.
split.
  intros x [ax | sx];[ rewrite ax; left; auto |].
  now simpl; right; destruct en as [it _]; apply it.
intros l' usubl'.
assert (al' : In a l').
  apply usubl'; left; reflexivity.
destruct (remove_elem a l' al') as [l2 Pl2].
assert (sl2 : forall x, s x -> In x l2).
  intros x sx.
  destruct (elem_removed_in _ _ _ x Pl2) as [xa | ?]; auto.
    now apply usubl'; right.
  now case nsa; rewrite <- xa.
rewrite (remove_length  _ _ _ Pl2); simpl.
enough (length l <= length l2) by lia.
now destruct en as [_ it]; apply it.
Qed.

Lemma card_add_elem [T : Type] (s : T -> Prop) (a : T):
  finite s -> ~ s a -> card (union (singleton a) s ) = card s + 1.
Proof.
intros fs ans.
assert (tmp := finite_Pcard s fs).
assert (tmp' := card_def _ tmp).
assert (card_add := (card_s s _ a tmp' ans)).
replace (card s + 1) with (S (card s)) by ring.
apply Pcard_card.
exact card_add.
Qed.

Lemma Penum_ext [T : Type] (s1 s2 : T -> Prop) l :
  (forall x, s1 x <-> s2 x) -> Penum s1 l <-> Penum s2 l.
Proof.
enough (main: forall (s s' : T -> Prop), (forall x, s x <-> s' x) ->
          Penum s l -> Penum s' l).
intros exteq; split; intros en.
  now apply (main s1); auto.
now apply (main s2); auto; intros x; apply and_comm; apply exteq.
clear s1 s2; intros s1 s2 exteq en1.
split.
  intros x; rewrite <- exteq; destruct en1 as [it _]; apply it.
intros l' s2subl'; assert (step : forall x, s1 x -> In x l').
  now intros x s1x; apply s2subl'; rewrite <- exteq.
now destruct en1 as [_ it]; apply it.
Qed.

Lemma Pcard_ext [T : Type] (s1 s2 : T -> Prop) n :
  (forall x, s1 x <-> s2 x) -> Pcard s1 n <-> Pcard s2 n.
Proof.
intros s1s2; split; intros [[l [sl Pn]] Pc2].
  assert (s2l : forall x, s2 x -> In x l).
    now intros x; rewrite <- s1s2; apply sl.
  split; [exists l; auto |].
  intros l' s'l'; apply Pc2; intros x; rewrite s1s2; auto.
assert (s1l : forall x, s1 x -> In x l).
    now intros x; rewrite s1s2; apply sl.
split; [exists l; auto |].
intros l' s'l'; apply Pc2; intros x; rewrite <- s1s2; auto.
Qed.

Lemma finite_ext [T : Type] (s1 s2 : T -> Prop) :
 (forall x, s1 x <-> s2 x) -> finite s1 <-> finite s2.
Proof.
intros s1s2; split; intros [l sl]; exists l; intros x; rewrite 1?s1s2; auto.
now rewrite <- s1s2; auto.
Qed.

Lemma card_ext [T : Type] (s1 s2 : T -> Prop) :
  finite s1 -> (forall x, s1 x <-> s2 x) -> card s1 = card s2.
Proof.
intros fs s1s2.
rewrite finite_has_minimal_list in fs; destruct fs as [l Pl1].
assert (Pl2 := Pl1); rewrite (Penum_ext _ _ _ s1s2) in Pl2.
now rewrite (enum_card _ _ Pl1), (enum_card _ _ Pl2).
Qed.

Lemma union_intersection_singleton [T : Type](s : T -> Prop) (a : T) :
  finite s ->
  s a ->
  forall x, union (singleton a) (intersection s (compl (singleton a))) x <->
            s x.
Proof.
intros fs sa x; split.
  now intros [ xa | [xs _]]; auto; rewrite xa.
intros sx; case (classic (x = a)).
  intros xa; rewrite xa; left; reflexivity.
now intros xna; right; split; auto.
Qed.

Lemma card_inter_compl [T : Type] (s : T -> Prop) (a : T):
 finite s ->
 s a -> card (intersection s (compl (singleton a)) )= card s - 1.
Proof.
intros fs sa.
assert (ext : forall x, s x <->
                 union (singleton a) (intersection s (compl (singleton a))) x).
  intros x; apply and_comm.
  apply union_intersection_singleton; auto.
rewrite (card_ext _ _ fs ext).
rewrite card_add_elem;[ lia | | ].
  now apply Intersection_preserves_Finite; left.
intros [_ it]; case it; reflexivity.
Qed.

Lemma empty_union [T : Type] (s1 s2 : T -> Prop) :
  (forall x, ~ s1 x) ->
   (forall x, union s1 s2 x <-> s2 x).
Proof.
intros s1empty.
intros x; split; intros xin.
  destruct xin as [abs | it]; auto.
  now case (s1empty x); auto.
now right; auto.
Qed.

Lemma Penum_rem_elem [T : Type] (s : T -> Prop) (a : T) (l : list T) :
  Penum s (a :: l) -> Penum (intersection (compl (singleton a)) s) l.
Proof.
intros sal.
split.
  intros x; case (classic (x = a)).
    intros xa; rewrite xa; intros [abs _]; case abs; reflexivity.
  intros xna [xna' sx]; destruct sal as [sal1 _]; apply sal1 in sx.
  simpl in sx; destruct sx as [ax | it]; auto.
  case xna; rewrite ax; reflexivity.
intros l' l'ctn.
assert (coverl' : forall x, s x -> In x (a :: l')).
  intros x sx; case (classic (a = x)).
    now intros ax; rewrite ax; simpl; auto.
  intros anx; simpl; right.
  apply l'ctn; split; [ | exact sx].
  now intros sgax; case anx; rewrite sgax.
destruct sal as [sal1 sal2]; apply sal2 in coverl'.
simpl in coverl'; lia.
Qed.

Lemma card_included_le [T : Type] (s1 s2 : T -> Prop) :
  finite s1 -> finite s2 ->
  (forall x, s1 x -> s2 x) ->
  card s1 <= card s2.
Proof.
intros f1 f2 incl.
assert (f1' := f1).
apply finite_Pcard in f1'.
destruct f1' as [n Pc1].
rewrite (Pcard_card _ _ Pc1).
destruct Pc1 as [_ nmin].
rewrite (finite_enum_card _ f2).
apply nmin.
intros x s1x; apply incl in s1x.
assert (Penum s2 (enum s2)) as [P2 _].
  apply enum_def.
  now rewrite <- finite_has_minimal_list.
now apply P2.
Qed.

Lemma card_union [T : Type] (s1 s2 : T -> Prop) :
  finite s1 -> finite s2 ->
  card (union s1 s2) = card s1 + card s2 - card (intersection s1 s2).
Proof.
rewrite finite_has_minimal_list.
intros [l1 h1].
revert s1 h1.
induction l1 as [ | a l1 Ihl1].
intros s1 s1init fs2.
assert (s1empty : forall x, ~ s1 x).
  now intros x s1x; destruct s1init as [A _]; case (A x).
assert (interempty : forall x, ~ (intersection s1 s2 x)).
  intros x ix; destruct s1init as [A _]; case (A x).
  destruct ix; auto.
  rewrite (card_0 _ s1empty), (card_0 _ interempty).
  replace (0 + card s2 - 0) with (card s2) by lia.
  apply card_ext.
  apply Union_preserves_Finite.
  assert(fs1: finite s1).
  now apply finite_0 in s1empty.
  auto.
  now apply empty_union.
intros s1 s1al1 fs2.
assert (f1 : finite s1) by now apply Penum_finite in s1al1.
assert (a1 : s1 a) by now apply (Penum_included _ _ s1al1); left.
set (s1' := intersection (compl (singleton a)) s1).
assert (s1'l1 : Penum s1' l1).
  now assert ( s1'i := Penum_rem_elem _ _ _ s1al1).
assert (fu : finite (union s1 s2)) by now apply Union_preserves_Finite.
assert (fi : finite (intersection s1 s2)).
  now apply Intersection_preserves_Finite; right.
assert (cs1 : card s1 = card s1' + 1).
  assert (same1 : forall x, s1 x <-> union (singleton a) s1' x).
    intros x; split.
      case (classic (singleton a x)); unfold union; auto.
      now intros nax; right; split; auto.
    intros [ax | [nax s1x]]; auto.
    now apply (Penum_included _ _ s1al1); left.
  rewrite (card_ext _ _ f1 same1).
  apply card_add_elem.
    now apply Intersection_preserves_Finite; right.
  now intros [ [] _].
case (classic (s2 a)).
  intros ains2.
  assert (same: forall x, union s1 s2 x <-> union s1' s2 x).
    intros x; case (classic (x = a)).
      now intros xa; rewrite xa; split; intros dummy; right.
    intros xna; split; (intros [s1x | s2x]; [ | right; easy]).
      left; split; [exact xna | exact s1x].
    now left; destruct s1x as [_ it].
  rewrite (card_ext _ _ fu same).
  rewrite (Ihl1 _ s1'l1 fs2).
  assert (ai : intersection s1 s2 a) by now split; auto.
  assert (samei : forall x, intersection s1 s2 x <->
           union (singleton a) (intersection s1' s2) x).
    intros x; split.
      intros [s1x s2x]; case (classic (x = a)).
        intros xa; rewrite xa; left; reflexivity.
      now intros xna; right; split; auto; split.
    intros [ax | xi].
      now split; auto; rewrite ax.
    now destruct xi as [[_ s1'x] s2x]; split; auto.
  assert (cs1s2 : card (intersection s1 s2) = card (intersection s1' s2) + 1).
    rewrite (card_ext _ _ fi samei), card_add_elem; auto.
      now apply Intersection_preserves_Finite; right.
    now intros [[abs _] _]; case abs.
  rewrite cs1s2.
  rewrite cs1.
  replace (card s1' + 1 + card s2) with (card s1' + card s2 + 1) by ring.
  lia.
intros ans2.
assert (sameu : forall x, union s1 s2 x <->
                          union (singleton a) (union s1' s2) x).
  intros x; split.
    case (classic (singleton a x)).
      now intros ax s1s2x; left.
    now intros nax [s1x | s2x]; unfold union; auto; right; left; split; auto.
  now intros [ax |[[nax s1x] | s2x]]; unfold union; auto; left; rewrite ax.
rewrite (card_ext _ _ fu sameu).
assert (fu' : finite (union s1' s2)).
  apply Union_preserves_Finite; split; auto.
  now apply Intersection_preserves_Finite; right.
assert (anu' : ~ union s1' s2 a).
  now intros [[[] _]| s2a];[ | case ans2; auto].
rewrite card_add_elem; auto.
assert (samei : forall x, intersection s1 s2 x <-> intersection s1' s2 x).
  intros x; split.
    case (classic (singleton a x)).
      now intros ax [_ s2x]; case ans2; rewrite <- ax.
    now intros anx [s1x s2x];split; auto; split; auto.
  now intros [[anx s1x] s2x]; split; auto.
rewrite (Ihl1 _ s1'l1); auto.
rewrite (card_ext _ _ fi samei).
rewrite cs1.
assert (iincl : forall x, intersection s1' s2 x -> s2 x).
  now intros x [_ it].
assert (fi' : finite (intersection s1' s2)).
  now apply Intersection_preserves_Finite; right.
assert (cmpcard := card_included_le _ _ fi' fs2 iincl).
lia.
Qed.

End FiniteSetFacts.



