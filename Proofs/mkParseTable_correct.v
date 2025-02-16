Require Import List.

Require Import Grammar.
Require Import Lemmas.
Require Import Tactics.
Require Import mkEntries_correct.

Import ListNotations.

Module GeneratorProofsFn (Import G : Grammar.T).

  Module Export EntryProofs := EntryProofsFn G.

  Definition table_correct_wrt_entries (tbl : parse_table) (es : list table_entry) :=
    forall x la p,
      pt_lookup x la tbl = Some p
      <-> x = (lhs p) /\ In (p, la) es.

  (* Shows that if a parse table is correct with respect to entries, and those entries are correct with respect to a grammar, 
     then the parse table is correct with respect to that grammar *)
  Lemma invariant_iff_parse_table_correct :
    forall (g : grammar) (es : list table_entry) (tbl : parse_table),
      entries_correct es g
      -> table_correct_wrt_entries tbl es
         <-> parse_table_correct tbl g.
  Proof.
    intros g es tbl Hwf.
    unfold entries_correct in Hwf.
    split.
    - intros Htc.
      unfold table_correct_wrt_entries in Htc.
      split.
      + unfold pt_sound.
        intros x x' la gamma f Hlk.
        apply Htc in Hlk; destruct Hlk as [Heq Hin]; subst; simpl in *.
        split; [auto | apply Hwf; auto].
      + unfold pt_complete.
        intros x la gamma f Hin Hlf.
        apply Htc; simpl.
        split; [auto | apply Hwf; auto].
    - intros Hpt.
      destruct Hpt as [Hsou Hcom].
      unfold table_correct_wrt_entries.
      intros x la [(x', gamma) f].
      split.
      + intros Hlk.
        apply Hsou in Hlk; destruct Hlk as [Heq [Hin Hlk]]; subst; simpl in *.
        split; [auto | apply Hwf; auto].
      + intros [Heq Hin]; subst; simpl in *.
        apply Hwf in Hin.
        destruct Hin as [Hin Hlf].
        apply Hcom; auto.
  Qed.

  (* mkParseTable soundness *)

  (* Proves that if addEntry returns a right value, its input must have been a right value *)
  Lemma addEntry_outer_right_inner_right :
    forall e s tbl,
      addEntry e s = inr tbl
      -> exists tbl',
        s = inr tbl'.
  Proof.
    intros e s tbl Hadd.
    unfold addEntry in Hadd.
    destruct s as [msg | tbl'] eqn:Hs; tc; subst.
    inv Hadd; eauto.
  Qed.

  (* Shows that adding a duplicate entry preserves the table correctness invariant *)
  Lemma duplicate_preserves_invariant :
    forall tbl es x la p,
      table_correct_wrt_entries tbl es
      -> pt_lookup x la tbl = Some p
      -> table_correct_wrt_entries tbl ((p, la) :: es).
  Proof.
    intros tbl es x la p Htc Hlk.
    unfold table_correct_wrt_entries.
    intros x' la' p'.
    split.
    - intros Hlk'.
      unfold table_correct_wrt_entries in Htc.
      apply Htc in Hlk'; destruct Hlk' as [Heq Hin]; split; auto.
      right; auto.
    - intros [Heq Hin]; subst.
      unfold table_correct_wrt_entries in Htc.
      inv Hin.
      + inv H; auto.
        pose proof Hlk as Hlk'.
        apply Htc in Hlk; destruct Hlk as [Heq Hin]; subst; auto.
      + apply Htc; auto.
  Qed.

  (* Proves that looking up an entry in a table after adding a new entry either returns the new entry or an existing one *)
  Lemma lookup_add_or :
    forall x x' la la' p p' tbl,
      pt_lookup x' la' (pt_add x la p tbl) = Some p'
      -> (x = x' /\ la = la' /\ p = p')
         \/ pt_lookup x' la' tbl = Some p'.
  Proof.
    intros x x' la la' p p' tbl Hlk.
    unfold pt_lookup in Hlk; unfold pt_add in Hlk.
    rewrite ParseTableFacts.add_o in Hlk.
    destruct (ParseTableFacts.eq_dec (x, la) (x', la')); auto.
    inv e; inv Hlk; auto.
  Qed.

  (* Shows that adding a new entry preserves the table correctness invariant *)
  Lemma new_entry_preserves_invariant :
    forall tbl es p la,
      table_correct_wrt_entries tbl es
      -> pt_lookup (lhs p) la tbl = None
      -> table_correct_wrt_entries (pt_add (lhs p) la p tbl) ((p, la) :: es).
  Proof.
    intros tbl es p la Htc Hlk.
    unfold table_correct_wrt_entries.
    intros x' la' p'.
    split.
    - intros Hlk'.
      apply lookup_add_or in Hlk'.
      inv Hlk'.
      + destruct H as [Hx [Hla Hgamma]]; subst; split; auto.
        left; auto.
      + apply Htc in H; destruct H as [Heq Hin]; subst; split; auto.
        right; auto.
    - intros [Heq Hin]; subst; inv Hin.
      + inv H.
        unfold pt_lookup.
        unfold pt_add.
        apply ParseTableFacts.add_eq_o; auto.
      + destruct (ParseTableFacts.eq_dec (lhs p, la) (lhs p', la')).
        * inv e.
          assert (Hand : lhs p = lhs p' /\ In (p', la') es) by auto.
          apply Htc in Hand; tc.
        * unfold pt_lookup.
          unfold pt_add.
          rewrite ParseTableFacts.add_neq_o; auto.
          apply Htc; auto.
  Qed.

  Definition unique_productions g : Prop :=
    NoDup (baseProductions g).

  Definition unique_action_per_prod (es : list table_entry) : Prop :=
    forall p f f' la,
      In (existT _ p f, la) es
      -> In (existT _ p f', la) es
      -> f = f'.

  Lemma p_in_ps_impl_b_in_baseProductions :
    forall b f ps,
      In (existT _ b f) ps -> In b (map baseProduction ps).
  Proof.
    intros b f xps Hin.
    eapply in_map with (f := baseProduction) in Hin; auto.
  Qed.

  Lemma unique_productions_unique_action_per_prod' :
    forall (ps : list production)
           (b : base_production)
           (f f' : action_ty b),
      NoDup (map baseProduction ps)
      -> In (existT _ b f)  ps
      -> In (existT _ b f') ps
      -> f = f'.
  Proof.
    intros ps.
    induction ps as [| p ps IH]; intros b f f' Hnd Hin Hin'; simpl in *.
    - inv Hin.
    - inv Hnd.
      destruct Hin as [Heq | Hin]; destruct Hin' as [Heq' | Hin']; subst; simpl in *; auto.
      + apply Eqdep_dec.inj_pair2_eq_dec; auto.
        apply base_production_eq_dec.
      + apply p_in_ps_impl_b_in_baseProductions in Hin'; tc.
      + apply p_in_ps_impl_b_in_baseProductions in Hin; tc.
  Qed.

  Lemma unique_productions_unique_action_per_prod :
    forall g es,
      unique_productions g
      -> entries_correct es g
      -> unique_action_per_prod es.
  Proof.
    intros g es Hu Hc.
    unfold unique_action_per_prod.
    intros p f f' la Hin Hin'.
    apply Hc in Hin ; destruct Hin  as [Hin _].
    apply Hc in Hin'; destruct Hin' as [Hin' _].
    eapply unique_productions_unique_action_per_prod'; eauto.
  Qed.

    Lemma addEntry_preserves_invariant :
    forall (e : table_entry)
           (es : list table_entry)
           (tbl' tbl : parse_table),
      table_correct_wrt_entries tbl' es
      -> addEntry e (inr tbl') = inr tbl
      -> unique_action_per_prod (e :: es)
      -> table_correct_wrt_entries tbl (e :: es).
  Proof.
    intros e es tbl' tbl Htc Hadd Hu.
    destruct e as (p, la) eqn:He.
    unfold addEntry in Hadd.
    destruct p as [(x, gamma) f].
    destruct (pt_lookup x la tbl') as [[(x', gamma') f'] |] eqn:Hlk.
    - destruct (Gen.L.base_production_eq_dec (x, gamma) (x', gamma')) as [Heq | Hneq].
      + inv Heq; inv Hadd.
        assert (f = f').
        { eapply Hu.
          - left; eauto.
          - apply Htc in Hlk; destruct Hlk as [Heq Hin].
            right; auto. }
        subst.
        eapply duplicate_preserves_invariant; eauto.
      + inv Hadd.
    - inv Hadd.
      apply new_entry_preserves_invariant with
          (p := existT _ (x, gamma) f); auto.
  Qed.

  (* Proves that an empty parse table is correct with respect to empty entries *)
  Lemma empty_table_correct_wrt_empty_entries :
    table_correct_wrt_entries empty_table [].
  Proof.
    unfold table_correct_wrt_entries.
    intros x gamma la.
    split.
    - intros Hlk.
      unfold pt_lookup in Hlk.
      rewrite ParseTableFacts.empty_o in Hlk; inv Hlk.
    - intros [Heq Hin]; inv Hin.
  Qed.

  (* Shows that unique action per production property is preserved when removing the head entry *)
  Lemma unique_action_per_prod_tl :
    forall e es,
      unique_action_per_prod (e :: es)
      -> unique_action_per_prod es.
  Proof.
    intros e es Hu.
    unfold unique_action_per_prod.
    intros p f f' la Hin Hin'.
    eapply Hu; right; eauto.
  Qed.

  (* Main soundness theorem for mkParseTable with respect to the invariant *)
  Lemma mkParseTable_sound_wrt_invariant :
    forall (es  : list table_entry)
           (tbl : parse_table),
      unique_action_per_prod es
      -> mkParseTable es = inr tbl
      -> table_correct_wrt_entries tbl es.
  Proof.
    intros es.
    induction es as [| e es]; intros tbl Hu Hmk; simpl in *.
    - inv Hmk.
      apply empty_table_correct_wrt_empty_entries.
    - pose proof Hmk as Hmk'.
      apply addEntry_outer_right_inner_right in Hmk.
      destruct Hmk as [tbl' Hmk].
      rewrite Hmk in Hmk'.
      pose proof Hu as Hu'; apply unique_action_per_prod_tl in Hu.
      eapply addEntry_preserves_invariant; eauto.
  Qed.

  (* Main soundness theorem for mkParseTable *)
  Lemma mkParseTable_sound :
    forall (es  : list table_entry)
           (g   : grammar)
           (tbl : parse_table),
      unique_productions g
      -> entries_correct es g
      -> mkParseTable es = inr tbl
      -> parse_table_correct tbl g.
  Proof.
    intros es g tbl Hu Hwf Hmk.
    eapply invariant_iff_parse_table_correct; eauto.
    apply mkParseTable_sound_wrt_invariant; auto.
    eapply unique_productions_unique_action_per_prod; eauto.
  Qed.

  (* mkParseTable completeness *)

  Lemma table_correct_wrt_empty_entries_eq_empty_table :
    forall tbl,
      table_correct_wrt_entries tbl []
      -> ParseTable.Equal tbl empty_table.
  Proof.
    intros tbl Htc.
    unfold ParseTable.Equal.
    intros (x, la).
    unfold table_correct_wrt_entries in Htc.
    destruct (pt_lookup x la tbl) as [gamma |] eqn:Hlk.
    - apply Htc in Hlk; destruct Hlk as [Heq Hin].
      inv Hin.
    - rewrite ParseTableFacts.empty_o; auto.
  Qed.

  Lemma invariant_cons_duplicate_invariant_tail :
    forall tbl p la es,
      table_correct_wrt_entries tbl ((p, la) :: es)
      -> In (p, la) es
      -> table_correct_wrt_entries tbl es.
  Proof.
    intros tbl p la es Htc Hin.
    unfold table_correct_wrt_entries.
    intros x la' p'.
    split.
    - intros Hlk.
      apply Htc in Hlk; destruct Hlk as [Heq Hin']; subst.
      split; auto.
      destruct Hin' as [Heq | Hin']; auto.
      inv Heq; auto.
    - intros [Heq Hin']; subst.
      apply Htc.
      split; [auto | right; auto].
  Qed.

  Lemma eq_keys_eq_gammas :
    forall tbl es p p' la,
      table_correct_wrt_entries tbl es
      -> In (p, la) es
      -> In (p', la) es
      -> lhs p = lhs p'
      -> rhs p = rhs p'.
  Proof.
    intros tbl es p p' la Htc Hin Hin' Hl.
    unfold table_correct_wrt_entries in Htc.
    assert (Hand : lhs p = lhs p
                   /\ In (p, la) es) by auto.
    assert (Hand' : lhs p = lhs p'
                    /\ In (p', la) es) by auto.
    apply Htc in Hand; apply Htc in Hand'; tc.
  Qed.

  Lemma invariant_cons_eq_gammas :
    forall tbl p p' la es,
      table_correct_wrt_entries tbl ((p, la) :: es)
      -> In (p', la) es
      -> lhs p = lhs p'
      -> rhs p = rhs p'.
  Proof.
    intros tbl p p' la es Htc Hin Hl.
    unfold table_correct_wrt_entries in Htc.
    assert (H : lhs p = lhs p
                /\ In (p, la) ((p, la) :: es))
      by (simpl; auto).
    assert (H' : lhs p = lhs p'
                 /\ In (p', la) ((p, la) :: es))
      by (simpl; auto).
    apply Htc in H; apply Htc in H'; tc.
  Qed.

  Lemma lhs_rhs_eq_uapp_prods_eq :
    forall p p' la es,
      lhs p = lhs p'
      -> rhs p = rhs p'
      -> In (p, la) es
      -> In (p', la) es
      -> unique_action_per_prod es
      -> p = p'.
  Proof.
    intros [(x, gamma) f] [(x', gamma') g] la es Hl Hr Hi Hi' Hu; simpl in *; subst.
    eapply Hu in Hi; eauto.
    apply Hi in Hi'; subst; auto.
  Qed.  
  
  (* BUG : originally had this as add instead of remove *)
  Lemma invariant_cons_new_entry_invariant_remove :
    forall tbl p la es,
      unique_action_per_prod ((p, la) :: es)
      -> table_correct_wrt_entries tbl ((p, la) :: es)
      -> ~In (p, la) es
      -> table_correct_wrt_entries (ParseTable.remove (lhs p, la) tbl) es.
  Proof.
    intros tbl p la es Hu Htc Hin.
    unfold table_correct_wrt_entries.
    intros x' la' p'.
    split.
    - intros Hlk.
      destruct (ParseTableFacts.eq_dec (lhs p, la) (x', la')).
      + inv e.
        unfold pt_lookup in Hlk.
        rewrite ParseTableFacts.remove_eq_o in Hlk; inv Hlk; auto.
      + unfold pt_lookup in Hlk.
        rewrite ParseTableFacts.remove_neq_o in Hlk; auto.
        unfold table_correct_wrt_entries in Htc.
        apply Htc in Hlk; destruct Hlk as [Heq Hin']; subst.
        split; auto.
        inv Hin'; tc.
    - intros [Heq Hin']; subst.
      destruct (ParseTableFacts.eq_dec (lhs p, la) (lhs p', la')).
      + inv e.
        assert (p = p').
        { eapply lhs_rhs_eq_uapp_prods_eq with
              (la := la')
              (es := ((p, la') :: es)); eauto.
          - eapply invariant_cons_eq_gammas in Htc; eauto.
          - left; auto.
          - right; auto. }
        subst; tc.
      + unfold pt_lookup.
        rewrite ParseTableFacts.remove_neq_o; auto.
        apply Htc; split; auto; right; auto.
  Qed.

  Definition pl_pair := (base_production * lookahead)%type.

  Definition plPairOf (e : table_entry) :=
    match e with
    | (existT _ p _, la) => (p, la)
    end.

  Definition plPairsOf (es : list table_entry) :=
    map plPairOf es.

  Lemma pl_pair_eq_dec :
    forall p p' : pl_pair,
      {p = p'} + {p <> p'}.
  Proof.
    repeat decide equality.
  Qed.

  Lemma in_plPairsOf_ex_in_entries :
    forall p la es,
      In (p, la) (plPairsOf es)
      -> exists f,
        In (existT _ p f, la) es.
  Proof.
    intros p la es Hin.
    unfold plPairsOf in Hin.
    eapply in_map_iff in Hin.
    destruct Hin as [e [Heq Hin]].
    destruct e as [(x, gamma) f]; simpl in *.
    inv Heq; eauto.
  Qed.

  Lemma not_in_plPairsOf_not_in_entries :
    forall p f la es,
      ~ In (p, la) (plPairsOf es)
      -> ~ In (existT _ p f, la) es.
  Proof.
    intros p f la es Hnin; unfold not; intros Hin; apply Hnin.
    unfold plPairsOf.
    apply in_map with (f := plPairOf) in Hin; auto.
  Qed.

  Lemma correct_post_table_implies_correct_pre_table :
    forall tbl e es,
      unique_action_per_prod (e :: es)
      -> table_correct_wrt_entries tbl (e :: es)
      -> exists tbl',
          table_correct_wrt_entries tbl' es.
  Proof.
    intros tbl e es Hu Htc.
    destruct (in_dec pl_pair_eq_dec (plPairOf e) (plPairsOf es)); subst; simpl in *.
    - destruct e as [[p f] la]; simpl in *.
      apply in_plPairsOf_ex_in_entries in i.
      destruct i as [g Hin].
      assert (f = g).
      { eapply Hu; [left; eauto | right; eauto]. }
      subst.
      exists tbl.
      eapply invariant_cons_duplicate_invariant_tail; eauto.
    - destruct e as ([(x,gamma) f], la); simpl in *.
      exists (ParseTable.remove (x, la) tbl).
      eapply invariant_cons_new_entry_invariant_remove in Htc; eauto.
      apply not_in_plPairsOf_not_in_entries; auto.
  Qed.

  Lemma invariant_tables_eq :
    forall tbl tbl' es,
      unique_action_per_prod es
      -> table_correct_wrt_entries tbl es
      -> table_correct_wrt_entries tbl' es
      -> ParseTable.Equal tbl tbl'.
  Proof.
    intros tbl tbl' es Hu Htc Htc'.
    unfold ParseTable.Equal.
    intros (x, la).
    destruct (ParseTable.find (x, la) tbl) as [p |] eqn:Hf.
    - destruct (ParseTable.find (x, la) tbl') as [p' |] eqn:Hf'.
      + apply Htc in Hf; destruct Hf as [Heq Hin]; subst.
        apply Htc' in Hf'; destruct Hf' as [Heq Hin']; subst.
        assert (p = p').
        { eapply lhs_rhs_eq_uapp_prods_eq; eauto.
          eapply eq_keys_eq_gammas; eauto. }
        subst; auto.
      + apply Htc in Hf; destruct Hf as [Heq Hin]; subst.
        unfold table_correct_wrt_entries in Htc'.
        assert (H : lhs p = lhs p /\ In (p, la) es) by auto.
        apply Htc' in H.
        unfold pt_lookup in H; tc.
    - destruct (ParseTable.find (x, la) tbl') as [p' |] eqn:Hf'.
      + apply Htc' in Hf'.
        apply Htc in Hf'.
        unfold pt_lookup in Hf'; congruence.
      + auto.
  Qed.

  Lemma invariant_not_in_add :
    forall tbl tbl' es p la,
      unique_action_per_prod ((p, la) :: es)
      -> table_correct_wrt_entries tbl es
      -> table_correct_wrt_entries tbl' ((p, la) :: es)
      -> ~In (p, la) es
      -> table_correct_wrt_entries (pt_add (lhs p) la p tbl) ((p, la) :: es).
  Proof.
    intros tbl tbl' es p la Hu Htc Htc' Hin.
    intros x' la' p'.
    split.
    - intros Hlk.
      unfold pt_lookup, pt_add in Hlk.
      destruct (ParseTableFacts.eq_dec (lhs p, la) (x', la')).
      + inv e.
        rewrite ParseTableFacts.add_eq_o in Hlk; auto.
        inv Hlk; split; auto; left; auto.
      + rewrite ParseTableFacts.add_neq_o in Hlk; auto.
        apply Htc in Hlk; destruct Hlk as [Heq Hin']; subst.
        split; auto; right; auto.
    - intros [Heq Hin']; subst.
      unfold pt_lookup, pt_add.
      inv Hin'.
      + inv H.
        rewrite ParseTableFacts.add_eq_o; auto.
      + destruct (ParseTableFacts.eq_dec (lhs p, la) (lhs p', la')).
        * inv e.
          assert (p = p').
          { eapply lhs_rhs_eq_uapp_prods_eq with
                (es := (p, la') :: es); eauto.
            - eapply eq_keys_eq_gammas; eauto.
              + left; auto.
              + right; auto.
            - left; auto.
            - right; auto. }
          subst.
          apply invariant_cons_eq_gammas with (p' := p') in Htc'; auto; tc.
        * rewrite ParseTableFacts.add_neq_o; auto.
          apply Htc; auto.
  Qed.

  Lemma add_preserves_equal :
    forall tbl tbl' x la p,
      ParseTable.Equal tbl tbl'
      -> ParseTable.Equal (pt_add x la p tbl) (pt_add x la p tbl').
  Proof.
    intros tbl tbl' x la p Heq.
    unfold ParseTable.Equal.
    intros (x', la').
    unfold pt_add.
    destruct (ParseTableFacts.eq_dec (x, la) (x', la')).
    - inv e.
      repeat rewrite ParseTableFacts.add_eq_o; auto.
    - repeat rewrite ParseTableFacts.add_neq_o; auto.
  Qed.

  Lemma addEntry_duplicate_doesn't_change_table :
    forall tbl es p la,
      table_correct_wrt_entries tbl es
      -> In (p, la) es
      -> addEntry (p, la) (inr tbl) = inr tbl.
  Proof.
    intros tbl es p la Htc Hin.
    unfold addEntry.
    destruct p as [(x, gamma) f].
    assert (H : x = lhs (existT _ (x, gamma) f)
                /\ In (existT _ (x, gamma) f, la) es) by auto.
    apply Htc in H.
    rewrite H.
    destruct (Gen.L.base_production_eq_dec (x, gamma) (x, gamma)); [auto | congruence].
  Qed.

  Lemma equal_preserves_invariant :
    forall tbl tbl' ps,
      table_correct_wrt_entries tbl ps
      -> ParseTable.Equal tbl tbl'
      -> table_correct_wrt_entries tbl' ps.
  Proof.
    intros tbl tbl' es Htc Heq.
    auto.
    unfold table_correct_wrt_entries in Htc.
    unfold pt_lookup in Htc.
    intros x gamma la.
    split; [intros Hlk | intros Hin].
    - apply Htc.
      unfold ParseTable.Equal in Heq.
      rewrite Heq; auto.
    - unfold pt_lookup. 
      rewrite <- Heq.
      apply Htc; auto.
  Qed.

  Lemma addEntry_new_entry_pt_add :
    forall tbl tbl' es p la,
      unique_action_per_prod ((p, la) :: es)
      -> table_correct_wrt_entries tbl es
      -> table_correct_wrt_entries tbl' ((p, la) :: es)
      -> ~ In (p, la) es
      -> addEntry (p, la) (inr tbl) = inr (pt_add (lhs p) la p tbl).
  Proof.
    intros tbl tbl' es p la Hu Htc Htc' Hin.
    destruct (pt_lookup (lhs p) la tbl) as [p' |] eqn:Hlk.
    - assert (p = p').
      (* lemma *)
      { apply Htc with (x := lhs p) in Hlk.
        destruct Hlk as [Heq Hin']; subst.
        eapply lhs_rhs_eq_uapp_prods_eq with
            (es := (p, la) :: es); eauto.
        - eapply eq_keys_eq_gammas; eauto.
          + left; auto.
          + right; auto.
        - left; auto.
        - right; auto. }
      subst.
      eapply Htc in Hlk; destruct Hlk as [Heq Hin']; subst; tc.
    - destruct p as [(x, gamma) f]; simpl in *.
      rewrite Hlk; auto.
  Qed.

  Lemma mkParseTable_complete_wrt_invariant :
    forall es tbl,
      unique_action_per_prod es
      -> table_correct_wrt_entries tbl es
      -> exists tbl',
          ParseTable.Equal tbl tbl'
          /\ mkParseTable es = inr tbl'.
  Proof.
    intros es.
    induction es as [| (p, la) es]; intros post_tbl Hu Htc.
    - apply table_correct_wrt_empty_entries_eq_empty_table in Htc.
      exists empty_table; auto.
    - pose proof Htc as Htc'.
      apply correct_post_table_implies_correct_pre_table in Htc.
      destruct Htc as [pre_tbl Htc].
      pose proof Htc as Htc''.
      apply IHes in Htc.
      destruct Htc as [pre_tbl' [Hpreq Hpremk]].
      destruct (in_dec pl_pair_eq_dec (plPairOf (p, la)) (plPairsOf es)).
      + destruct p as [(x, gamma) f]; simpl in *.
        apply in_plPairsOf_ex_in_entries in i.
        destruct i as [f' Hin].
        assert (f = f').
        { unfold unique_action_per_prod in Hu.
          eapply Hu with (p := (x, gamma)).
          - left; auto.
          - right; auto. }
        subst.
        exists pre_tbl'; split.
        * apply invariant_cons_duplicate_invariant_tail in Htc'; auto.
          -- apply ParseTableFacts.Equal_trans with (m' := pre_tbl); auto.
             eapply invariant_tables_eq with (es := es); eauto.
             eapply unique_action_per_prod_tl; eauto.
        * simpl.
          rewrite Hpremk.
          eapply addEntry_duplicate_doesn't_change_table; eauto.
          eapply equal_preserves_invariant; eauto.
      + exists (pt_add (lhs p) la p pre_tbl'); split.
        * eapply invariant_not_in_add in Htc''; eauto.
          -- apply add_preserves_equal with 
                 (x  := lhs p)
                 (la := la)
                 (p := p) in Hpreq; eauto.
             apply invariant_tables_eq with (tbl := post_tbl) in Htc''; auto.
             apply ParseTableFacts.Equal_trans with
                 (m' := pt_add (lhs p) la p pre_tbl); auto.
          -- destruct p as [(x, gamma) f]; simpl in *.
             apply not_in_plPairsOf_not_in_entries; auto.
        * simpl.
          rewrite Hpremk.
          eapply addEntry_new_entry_pt_add; eauto.
          -- eapply equal_preserves_invariant; eauto.
          -- destruct p as [(x, gamma) f]; simpl in *.
             apply not_in_plPairsOf_not_in_entries; auto.
      + eapply unique_action_per_prod_tl; eauto.
      + auto.
  Qed.

  Lemma mkParseTable_complete :
    forall (es  : list table_entry)
           (g   : grammar)
           (tbl : parse_table),
      unique_productions g
      -> entries_correct es g
      -> parse_table_correct tbl g
      -> exists tbl',
          ParseTable.Equal tbl tbl'
          /\ mkParseTable es = inr tbl'.
  Proof.
    intros es g tbl Hup Hwf Hpt.
    apply mkParseTable_complete_wrt_invariant.
    - eapply unique_productions_unique_action_per_prod; eauto.
    - eapply invariant_iff_parse_table_correct; eauto.
  Qed.
  
End GeneratorProofsFn.

