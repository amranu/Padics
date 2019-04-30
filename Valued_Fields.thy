theory Valued_Fields
  imports  Main "~~/src/HOL/Algebra/Ring"
                "~~/src/HOL/Algebra/QuotRing"  
                "~~/src/HOL/Algebra/Valued_Fields/Extended_OAG"
                "~~/src/HOL/Algebra/Subrings"
                "~~/src/HOL/Algebra/Ideal"

begin

declare [[ smt_timeout = 6000 ]]

record ('a, 'b) valued_ring =
  ring :: "'a ring" ("K\<index>") 
  val_group::  "'b extended_ordered_monoid" ("\<Gamma>\<index>")
  ord :: "'a \<Rightarrow> 'b" ("\<nu>\<index>")

(*Definition of the valuation ring of a valued ring G. It is defined as the subring of "ring G"
consisting of elements of positive valuation.*)


definition 
  valuation_ring :: "('a,'b, 'm) valued_ring_scheme \<Rightarrow> 'a ring" ("\<O>\<index>") 
  where "valuation_ring G = \<lparr>carrier = {x.( x \<in> (carrier (ring G)) 
                                  \<and> \<one>\<^bsub>val_group G\<^esub> \<preceq>\<^bsub>val_group G\<^esub> (\<nu>\<^bsub>G\<^esub> x))},
                             mult = mult (ring G),
                             one = \<one>\<^bsub>(ring G)\<^esub> ,
                             zero = \<zero>\<^bsub>(ring G)\<^esub>, 
                             add = add (ring G)\<rparr> "

definition
  maximal_ideal:: "('a,'b, 'm) valued_ring_scheme \<Rightarrow> 'a set" ("\<mm>\<index>")
  where "maximal_ideal G = {x. x \<in> (carrier (ring G)) 
                            \<and> \<one>\<^bsub>val_group G\<^esub>\<preceq>\<^bsub>val_group G\<^esub> (\<nu>\<^bsub>G\<^esub> x) 
                            \<and> \<one>\<^bsub>val_group G\<^esub> \<noteq>(\<nu>\<^bsub>G\<^esub> x)}"

definition 
  residue_field :: "('a,'b, 'm) valued_ring_scheme \<Rightarrow> 'a set ring" ("k\<index>")
  where "residue_field G = \<O>\<^bsub>G\<^esub> Quot (\<mm>\<^bsub>G\<^esub>)"

(*Predicate for a function from a ring to an extended OAG which obeys the ultrametric inequality*)

abbreviation 
  is_ultrametric :: "[('a, 'm) ring_scheme, ('b, 'n) extended_ordered_monoid_scheme, 'a \<Rightarrow>'b ] => bool"
  where "is_ultrametric R S h \<equiv>  (\<forall> x. x \<in> carrier R \<longrightarrow> (h x) \<in> carrier S \<union> {\<infinity>\<^bsub>S\<^esub>}) \<and>
                                 ( \<forall> x y. x \<in> carrier R \<and> y \<in> carrier R 
                                          \<longrightarrow> (le S (Min\<^bsub>S\<^esub>  (h x) (h y))  ( h (x\<oplus>\<^bsub>R\<^esub>y)) ))"

(*Predicate for the set of nonzero elements in a ring *)
abbreviation 
  nonzero :: "('a, 'm) ring_scheme \<Rightarrow> 'a set"
  where "nonzero R \<equiv> {x. x \<in> carrier R \<and> x \<noteq> (zero R)}"

(*Predicate for a function from a ring to an extended
 OAG which is multiplicative on nonzero ring elements*)

abbreviation 
  multiplicative :: "[('a, 'm) ring_scheme, ('b, 'n) extended_ordered_monoid_scheme, 'a \<Rightarrow>'b ] => bool"
  where "multiplicative R S h \<equiv> ( \<forall> x y. x \<in> nonzero R 
                                        \<and> y \<in> nonzero R 
                                      \<longrightarrow> h(x \<otimes>\<^bsub>R\<^esub>y) =  (h x)\<otimes>\<^bsub>S\<^esub>(h y)) "

(*Predicate for a function from a ring to an extended OAG which sends units to true group elements*)

abbreviation 
  nonzero_to_group :: "[('a, 'm) ring_scheme, ('b, 'n) extended_ordered_monoid_scheme, 'a \<Rightarrow>'b ] => bool"
  where "nonzero_to_group R S h \<equiv> (\<forall> x. (x \<in> carrier R \<and> (x \<noteq> \<zero>\<^bsub>R\<^esub>)) \<longrightarrow> (h x) \<in> carrier S)"

(*Definition for the set of valuations from a fixed ring to a fixed OAG*)


definition
  valuation :: "[('a, 'm) ring_scheme, ('b, 'n) extended_ordered_monoid_scheme] => ('a => 'b) set"
  where "valuation R S =
    {h. h \<in> carrier R \<rightarrow> vals S   \<and> (is_ultrametric R S h) 
                                  \<and> (multiplicative R S h)
                                  \<and> (nonzero_to_group R S h)
                                  \<and> (h \<zero>\<^bsub>R\<^esub>) = \<infinity>\<^bsub>S\<^esub> 
                                  \<and> (h \<one>\<^bsub>R\<^esub>) = \<one>\<^bsub>S\<^esub> }"


(*Locale for a valued integral domain*)

locale valued_ring = 
  fixes G (structure)
  assumes a_domain:
    "Ring.domain K"
  assumes a_val_group:
    "extended_ordered_abelian_group \<Gamma>"
  assumes a_valuation:
    "\<nu> \<in> valuation K \<Gamma>"

fun (in ring)
int_const :: "int \<Rightarrow> 'a" ("c\<index>") where
"int_const n = Group.pow (add_monoid R) \<one>\<^bsub>R\<^esub> n"


lemma (in valued_ring) ultrametric:   
    assumes "x \<in> carrier K"
    assumes "y \<in> carrier K"
    shows " (Min\<^bsub>\<Gamma>\<^esub>   (\<nu> x) (\<nu> y))\<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x\<oplus>\<^bsub>K\<^esub>y) "
proof-
  have "x \<in> carrier K \<and> y \<in> carrier K \<longrightarrow>(Min\<^bsub>\<Gamma>\<^esub>  (\<nu> x) (\<nu> y)) \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x\<oplus>\<^bsub>K\<^esub>y) "
    using a_valuation valuation_def by (simp add: valuation_def)
  from this show  "(Min\<^bsub>\<Gamma>\<^esub>  (\<nu> x) (\<nu> y))\<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x\<oplus>\<^bsub>K\<^esub>y) " using assms(1) assms(2) by blast
qed

lemma (in ring) const_one:
"c\<^bsub>1\<^esub> = \<one>\<^bsub>R\<^esub>"
  by (metis add.int_pow_1 add_pow_def int_const.elims one_closed)

lemma (in ring)
"c\<^bsub>(n + 1)\<^esub> = c\<^bsub>n\<^esub> \<oplus>\<^bsub>R\<^esub> \<one>\<^bsub>R\<^esub>"
  by (metis add.int_pow_mult add_pow_def
      const_one int_const.simps one_closed) 


lemma (in valued_ring) val_ring_subset:
  assumes "x \<in> carrier \<O>"
  shows "x \<in> carrier K" 
  by (metis (no_types, lifting)
      assms mem_Collect_eq 
      partial_object.select_convs(1) 
      valuation_ring_def) 

lemma (in valued_ring) val_range:
  assumes "x \<in> carrier K"
  shows "\<nu> x \<in> vals \<Gamma>"
  using a_valuation valuation_def by (simp add: valuation_def assms)

lemma (in valued_ring) multiplicative:
  assumes "x \<in> carrier K"
  assumes "y \<in> carrier K"
  shows "\<nu> (x \<otimes>\<^bsub>K\<^esub> y) = (\<nu> x) \<otimes>\<^bsub>\<Gamma>\<^esub> (\<nu> y)"
proof-
  have M: "(multiplicative K \<Gamma> \<nu>)"
    using a_valuation by (simp add: valuation_def)
  from this show  "\<nu> (x  \<otimes>\<^bsub>K\<^esub> y) = (\<nu> x) \<otimes>\<^bsub>\<Gamma>\<^esub> (\<nu> y)"
  proof (cases "(x = \<zero>\<^bsub>K\<^esub>) \<or> ( y = \<zero>\<^bsub>K\<^esub>)")
    case True
    then have "x \<otimes>\<^bsub>K\<^esub> y = \<zero>\<^bsub>K\<^esub>" 
      by (simp add: a_domain assms(1) assms(2) domain.integral_iff)
    then have LHS: "\<nu> (x \<otimes>\<^bsub>K\<^esub> y) = \<infinity>\<^bsub>\<Gamma>\<^esub>"
      using a_valuation valuation_def by auto
    from True have "\<nu> x = \<infinity>\<^bsub>\<Gamma>\<^esub> \<or> \<nu> y = \<infinity>\<^bsub>\<Gamma>\<^esub>"
      using LHS \<open>x \<otimes>\<^bsub>K\<^esub> y = \<zero>\<^bsub>K\<^esub>\<close> by auto
    from this LHS val_range show "\<nu> (x \<otimes>\<^bsub>K\<^esub> y) = (\<nu> x) \<otimes>\<^bsub>\<Gamma>\<^esub> (\<nu> y)"
      by (simp add: extended_ordered_abelian_group.add_infinityOR a_val_group assms(1) assms(2))
  next
    case False
    from this  a_valuation and valuation_def have 0: "x \<in> nonzero K" 
      using assms(1) by blast
    from False  a_valuation and valuation_def have 1: "y \<in> nonzero K" 
      using assms(2) by blast
    from 0 and 1 and M show "\<nu>(x \<otimes>\<^bsub>K\<^esub> y) =  (\<nu> x)\<otimes>\<^bsub>\<Gamma>\<^esub>(\<nu> y)" by blast
  qed
qed   

lemma (in valued_ring) inv_simpR:
  assumes "x \<in> Units K"
  shows "inv\<^bsub>K\<^esub> x \<otimes>\<^bsub>K\<^esub>  x = \<one>\<^bsub>K\<^esub>" 
  by (meson assms Ring.ring_def a_domain cring.axioms(1)
      domain_def monoid.Units_l_inv)

lemma (in valued_ring) inv_simpL:
  assumes "x \<in> Units K"
  shows "x \<otimes>\<^bsub>K\<^esub> inv\<^bsub>K\<^esub> x = \<one>\<^bsub>K\<^esub>" 
  using inv_simpR a_domain Units_def assms 
        comm_monoid.comm_inv_char cring_def 
        domain.axioms(1) by fastforce

lemma (in valued_ring) nonzero_val:
  assumes "(x \<in> carrier K \<and> (x \<noteq> \<zero>\<^bsub>K\<^esub>))"
  shows "(\<nu> x) \<in> carrier \<Gamma>"
proof-
  have "(x \<in> carrier K \<and> (x \<noteq> \<zero>\<^bsub>K\<^esub>)) \<longrightarrow> (\<nu> x) \<in> carrier \<Gamma>"  
    using a_valuation by (simp add: valuation_def)
  from this and assms(1) show "(\<nu> x) \<in> carrier \<Gamma>" by auto
qed

lemma (in valued_ring) nonzero_val2:
  assumes "x \<in> Units K"
  shows "(\<nu> x) \<in> carrier \<Gamma>"
  using Ring.ring_def a_domain cring_def domain.axioms(1)
        domain.integral_iff domain.one_not_zero monoid.Units_inv_closed
        monoid.Units_r_inv valued_ring.nonzero_val valued_ring_axioms 
        by (metis assms monoid.Units_closed)




lemma (in valued_ring) val_zero:
  "\<nu> \<zero>\<^bsub>K\<^esub> = \<infinity>\<^bsub>\<Gamma>\<^esub>"
  using a_valuation by (simp add: valuation_def)

lemma (in valued_ring) val_one:
  "\<nu> \<one>\<^bsub>K\<^esub> = \<one>\<^bsub>\<Gamma>\<^esub>"
  using a_valuation by (simp add: valuation_def)

lemma (in valued_ring) val_neg_1:
  shows  "\<nu> (\<ominus>\<^bsub>K\<^esub> \<one>\<^bsub>K\<^esub>) = \<one>\<^bsub>\<Gamma>\<^esub>"
proof-
  have C0: "(\<ominus>\<^bsub>K\<^esub> \<one>\<^bsub>K\<^esub>) \<otimes>\<^bsub>K\<^esub> (\<ominus>\<^bsub>K\<^esub> \<one>\<^bsub>K\<^esub>) = \<one>\<^bsub>K\<^esub>" 
    by (simp add: a_domain cring.cring_simprules(12) 
      cring.cring_simprules(21) cring.cring_simprules(28) 
      cring.cring_simprules(3) cring.cring_simprules(6) 
      domain.axioms(1))
  then have C1: "\<nu> (\<one>\<^bsub>K\<^esub>) = \<nu> (\<ominus>\<^bsub>K\<^esub> \<one>\<^bsub>K\<^esub>) \<otimes>\<^bsub>\<Gamma>\<^esub> \<nu> (\<ominus>\<^bsub>K\<^esub> \<one>\<^bsub>K\<^esub>)" 
    using multiplicative a_domain cring.cring_simprules(3) 
          cring.cring_simprules(6) domain.axioms(1) by force
  from ordered_abelian_group.no_idempotents1 show " \<nu> (\<ominus>\<^bsub>K\<^esub> \<one>\<^bsub>K\<^esub>)  =  \<one>\<^bsub>\<Gamma>\<^esub>" 
    by (metis C0 C1 a_domain a_val_group cring.cring_simprules(3)
      cring.cring_simprules(6) domain.axioms(1) domain.integral_iff
      extended_ordered_abelian_group.axioms(1) val_one 
      valued_ring.nonzero_val valued_ring_axioms)
qed

lemma (in valued_ring) val_add_inv:
  assumes "x \<in> carrier K"
  shows  "\<nu> (\<ominus>\<^bsub>K\<^esub> x) = \<nu> x "
proof-
  have C0: "\<ominus>\<^bsub>K\<^esub> x = x \<otimes>\<^bsub>K\<^esub> (\<ominus>\<^bsub>K\<^esub> \<one>\<^bsub>K\<^esub>)"
  using Ring.ring_def a_domain assms cring_def domain.axioms(1) ring.r_minus by fastforce
  then show  "\<nu> (\<ominus>\<^bsub>K\<^esub> x) = \<nu> x "
    by (metis multiplicative val_neg_1 Ring.ring_def a_domain  assms 
        cring.cring_simprules(3) 
        cring_def domain.axioms(1) 
        monoid.one_closed monoid.r_one
        val_one) 
qed

lemma (in valued_ring) val_sum:
  assumes "x \<in> carrier K"
  assumes "y \<in> carrier K"
  shows "\<nu> (x \<oplus>\<^bsub>K\<^esub> y) \<in> vals \<Gamma>" 
  by (meson a_domain assms(1) assms(2)
      cring.cring_simprules(1) domain_def val_range)

lemma (in valued_ring) one_is_val:
  "\<one>\<^bsub>\<Gamma>\<^esub> \<in> vals \<Gamma>"
  by (metis a_domain cring.cring_simprules(6)
      domain.axioms(1) val_one
      valued_ring.val_range valued_ring_axioms) 

lemma (in valued_ring) one_in_group:
  "\<one>\<^bsub>\<Gamma>\<^esub> \<in> carrier \<Gamma>" 
  by (simp add: a_val_group 
      extended_ordered_abelian_group.axioms(1)
      ordered_abelian_group.one_in)

lemma (in valued_ring) in_val_ring:
  assumes "x \<in> carrier K"
  assumes "\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x" 
  shows "x \<in> carrier \<O>"
  using assms(1) assms(2) val_zero by (simp add: valuation_ring_def)

lemma (in valued_ring) in_val_ring_conv:
  assumes "x \<in> carrier K"
  assumes "x \<in> carrier \<O>"
  shows "\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x"
  by (metis (no_types, lifting) assms(2) 
      mem_Collect_eq partial_object.select_convs(1)
      valuation_ring_def)

locale valued_field = valued_ring + 
  assumes a_field:
    "Ring.field (ring G)"
  assumes val_surj:
    "surj \<nu>"


lemma (in valued_ring) prod_inequality:
  assumes "\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x"
  assumes "x \<in> carrier K"
  assumes "a \<in> carrier K"
  shows   "\<nu> a \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x \<otimes>\<^bsub>K\<^esub> a)"
proof-
  have C1:"\<nu> x \<in> vals \<Gamma>"
    using assms(2) val_range by auto 
  have C2: "\<nu> a \<in> vals \<Gamma>"
    using assms(3) val_range by auto  
  have "\<one>\<^bsub>\<Gamma>\<^esub> \<otimes>\<^bsub>\<Gamma>\<^esub> \<nu> a \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x  \<otimes>\<^bsub>\<Gamma>\<^esub> \<nu> a" 
    using assms(1) C1 C2 one_is_val
    by (simp add: extended_ordered_abelian_group.E_le_resp_mult a_val_group)
  from this and multiplicative show  "\<nu> a \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x \<otimes>\<^bsub>K\<^esub> a)"
    by (metis a_domain assms(2) assms(3) cring.cring_simprules(12)
        cring.cring_simprules(6) domain.axioms(1) val_one)
qed

lemma (in valued_ring) prod_chain:
  assumes "\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x"
  assumes "x \<in> carrier K"
  assumes "a \<in> carrier K"
  assumes "\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> a"
  assumes "\<one>\<^bsub>\<Gamma>\<^esub> \<noteq> \<nu> a"
  shows  "\<one>\<^bsub>\<Gamma>\<^esub> \<noteq> \<nu> (x \<otimes>\<^bsub>K\<^esub> a)"
proof
  assume 0: "\<one>\<^bsub>\<Gamma>\<^esub> = \<nu> (x \<otimes>\<^bsub>K\<^esub> a)"
  show False
  proof-
    from prod_inequality have "\<nu> a \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x \<otimes>\<^bsub>K\<^esub> a)" 
      using assms(1) assms(2) assms(3) by blast
    from this and 0 have  "\<nu> a \<preceq>\<^bsub>\<Gamma>\<^esub> \<one>\<^bsub>\<Gamma>\<^esub>"  by simp
    from this and assms(4) have "\<one>\<^bsub>\<Gamma>\<^esub> = \<nu> a" 
      by (meson a_val_group assms(3) 
        extended_ordered_abelian_group.chain 
        one_is_val valued_ring.val_range valued_ring_axioms)
    from this and assms(5) show False by auto
qed
qed

lemma (in valued_ring) val_of_inverse:
  assumes D: "x \<in> carrier K"
  assumes U: "x \<in> Units K"
  shows "inv\<^bsub>\<Gamma>\<^esub> (\<nu> x) = \<nu> (inv\<^bsub>K\<^esub> x)"
proof-
  from D and U have Q: "inv\<^bsub>K\<^esub> x \<in> carrier K"
    by (meson Ring.ring_def a_domain cring_def
        domain_def monoid.Units_inv_closed) 
  have P: "\<nu> (x \<otimes>\<^bsub>K\<^esub> inv\<^bsub>K\<^esub> x) = (\<nu> x) \<otimes>\<^bsub>\<Gamma>\<^esub> \<nu> (inv\<^bsub>K\<^esub> x)" 
    using Q D multiplicative by blast
  have "\<exists> y \<in> carrier K. x \<otimes>\<^bsub>K\<^esub> y = \<one>\<^bsub>K\<^esub> " 
    using monoid.Units_r_inv_ex U Ring.ring_def 
          a_domain cring_def domain.axioms(1) by metis
  from this have "x \<otimes>\<^bsub>K\<^esub> inv\<^bsub>K\<^esub> x = \<one>\<^bsub>K\<^esub>"
    using U inv_simpL by blast
  from this and P have "\<nu> \<one>\<^bsub>K\<^esub> = (\<nu> x) \<otimes>\<^bsub>\<Gamma>\<^esub> (\<nu> (m_inv K x))"
    by simp
  from this have  "\<exists> y \<in> carrier \<Gamma>. (\<nu> x) \<otimes>\<^bsub>\<Gamma>\<^esub> y = \<one>\<^bsub>\<Gamma>\<^esub> " 
    by (metis D Q \<open>x \<otimes>\<^bsub>K\<^esub> inv\<^bsub>K\<^esub> x = \<one>\<^bsub>K\<^esub>\<close> a_domain 
        domain.integral_iff domain.one_not_zero val_one
        valued_ring.nonzero_val valued_ring_axioms)
  from this show  "m_inv \<Gamma> (\<nu> x) =\<nu> (m_inv K x)" 
    by (metis D Q \<open>x \<otimes>\<^bsub>K\<^esub> inv\<^bsub>K\<^esub> x = \<one>\<^bsub>K\<^esub>\<close> a_domain
        a_val_group cring.cring_simprules(14) domain.axioms(1)
        domain.integral_iff domain.one_not_zero extended_ordered_abelian_group.axioms(1)
        monoid.inv_char multiplicative ordered_abelian_group_def ordered_monoid_def 
        val_one valued_ring.nonzero_val valued_ring_axioms)
qed

lemma (in valued_ring) val_inverse_or:
  assumes D: "x \<in> carrier K"
  assumes U: "x \<in> Units K"
  shows " \<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> (\<nu> (m_inv K x)) \<or>  \<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x"
proof-
  from D and U nonzero_val have 0: "\<nu> x \<in> carrier \<Gamma>"  
    by (simp add: nonzero_val2)
  from this and val_of_inverse have 1:" \<nu> (m_inv K x) \<in> carrier \<Gamma>" 
    by (meson Ring.ring_def U a_domain
        cring_def domain.axioms(1) monoid.Units_inv_Units
        nonzero_val2)
  then show " \<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (m_inv K x) \<or>  \<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x" 
    by (metis 0 1  ordered_abelian_group.inv_or
        Ring.ring_def U a_domain a_val_group cring_def 
        domain.axioms(1) extended_ordered_abelian_group.axioms(1)
        monoid.Units_inv_Units monoid.Units_inv_closed 
        monoid.Units_inv_inv ordered_abelian_group.inv_1 val_of_inverse)
qed

lemma (in valued_field) nonzero_val_conv:
  assumes  "(\<nu> x) \<in> carrier \<Gamma>"
  assumes "x \<in> carrier K"
  shows "x \<in> Units K"  (**)
proof-
  from assms have "\<nu> x \<noteq> \<infinity>\<^bsub>\<Gamma>\<^esub>" 
    using a_val_group extended_ordered_abelian_group.infinity_distinct by force 
  from this  assms val_zero have "x \<noteq> \<zero>\<^bsub>K\<^esub>" 
    by blast 
  from this show "x \<in> Units K" using a_field assms field.field_Units by blast
qed

lemma (in valued_field) val_ring_units:
  assumes "x \<in> carrier \<O>"
  assumes "\<nu> x = \<one>\<^bsub>\<Gamma>\<^esub>"
  shows "x \<in> Units \<O>"
proof-
  have car: "x \<in> carrier K" 
    by (simp add: assms(1) val_ring_subset)
  then have C1: "x \<in> Units K"
    using assms(2) one_is_val a_field 
          field.field_Units nonzero_val_conv 
    by (simp add: one_in_group)
  then  have "inv\<^bsub>\<Gamma>\<^esub> \<nu> x =\<nu> (inv\<^bsub>K\<^esub> x)"
    using car val_of_inverse assms(1) by blast
  from this and assms(2) have " \<one>\<^bsub>\<Gamma>\<^esub> =\<nu> (inv\<^bsub>K\<^esub> x)"
    using Ring.ring_def a_domain cring.cring_simprules(6) 
      cring_def domain.axioms(1) monoid.Units_one_closed 
      monoid.inv_one val_of_inverse val_one by fastforce
  from this have C2: " \<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (inv\<^bsub>K\<^esub>x)" 
    using C1 assms(2) car val_inverse_or by force
  have "x \<noteq> \<zero>\<^bsub>K\<^esub>" 
    using C1 a_val_group assms(2) extended_ordered_abelian_group.infinity_distinct
      one_in_group val_zero by force 
  from this car a_field C1 have "inv\<^bsub>K\<^esub>x \<in> carrier K" 
  proof -
    have "(x \<in> carrier K \<and> (\<exists>a. a \<in> carrier K \<and> a \<otimes>\<^bsub>K\<^esub> x = \<one>\<^bsub>K\<^esub> \<and> x \<otimes>\<^bsub>K\<^esub> a = \<one>\<^bsub>K\<^esub>))
           \<and> Group.comm_monoid K"
    using C1 Units_def a_domain cring_def domain.axioms(1) by fastforce
  then show ?thesis
    by (metis (no_types) comm_monoid.comm_inv_char)
  qed
  from this have C3:"inv\<^bsub>K\<^esub>x \<in> carrier \<O>"
    by (simp add: \<open>\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (inv\<^bsub>K\<^esub> x)\<close> in_val_ring)
  from m_inv_def C1 have C4: "inv\<^bsub>K\<^esub>x \<otimes>\<^bsub>K\<^esub> x = \<one>\<^bsub>K\<^esub>"
    using Ring.ring_def a_domain cring_def domain_def monoid.Units_l_inv by fastforce
  from this and C3 have "(inv\<^bsub>K\<^esub> x) \<in> carrier \<O> 
                        \<and> inv\<^bsub>K\<^esub>x \<otimes>\<^bsub>K\<^esub> x = \<one>\<^bsub>K\<^esub> 
                        \<and> (m_inv K x) \<otimes>\<^bsub>K\<^esub>  x = \<one>\<^bsub>K\<^esub>" 
    by blast
  from C1 and C3 have "inv\<^bsub>K\<^esub>x \<in> carrier \<O> 
                     \<and> inv\<^bsub>K\<^esub>x \<otimes>\<^bsub>\<O>\<^esub> x = \<one>\<^bsub>\<O>\<^esub>"
    by (simp add: C4 valuation_ring_def) 
  from this have "\<exists> y \<in> carrier (valuation_ring G). 
                  y \<otimes>\<^bsub>(valuation_ring G)\<^esub> x = \<one>\<^bsub>(valuation_ring G)\<^esub>
                \<and> x \<otimes>\<^bsub>(valuation_ring G)\<^esub>  y = \<one>\<^bsub>(valuation_ring G)\<^esub>" 
    by (metis (no_types, lifting) \<open>inv\<^bsub>K\<^esub> x \<in> carrier K\<close>
        a_domain car cring.cring_simprules(14) 
        domain.axioms(1) monoid.select_convs(1) 
        valuation_ring_def)
  from this and Units_def show "x \<in> Units (valuation_ring G)" 
    by (simp add: Units_def assms(1))
qed

lemma (in valued_ring) val_ring_minus0:
" x \<in> carrier \<O> \<Longrightarrow> (\<ominus>\<^bsub>K\<^esub> x) \<in> carrier \<O>"
proof-
 assume "x \<in> carrier (valuation_ring G)"
 then have "\<nu> (\<ominus>\<^bsub>K\<^esub> x) = \<nu> x "  
   by (simp add: val_ring_subset 
      valued_ring.val_add_inv valued_ring_axioms) 
 from this show "(\<ominus>\<^bsub>K\<^esub> x) \<in> carrier (valuation_ring G)" 
    by (simp add: \<open>x \<in> carrier \<O>\<close> a_domain cring.cring_simprules(3)
        domain.axioms(1) in_val_ring valued_ring.in_val_ring_conv 
        valued_ring.val_ring_subset valued_ring_axioms) 
qed

lemma (in valued_ring) val_ring_subring:
  "subring (carrier \<O>) (K)"
proof-
  have C0: "carrier \<O> \<subseteq> carrier K" 
    by (simp add: subsetI val_ring_subset) 
  have T: "\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<one>\<^bsub>\<Gamma>\<^esub>"
    using one_is_val
    by(simp add: extended_ordered_abelian_group.refl a_val_group) 
  have "\<one>\<^bsub>K\<^esub> \<in> carrier K"
    using valuation_ring_def val_one a_domain 
          cring.cring_simprules(6) domain.axioms(1)
          by blast 
  then have C1: "\<one>\<^bsub>K\<^esub> \<in> carrier \<O>" using T val_one
    by (simp add: valued_ring.in_val_ring valued_ring_axioms) 
  have C2: "\<And>x. x \<in> carrier \<O> \<Longrightarrow> \<ominus>\<^bsub>K\<^esub> x \<in> carrier \<O>"
    proof-
    fix x
    show "x \<in> carrier \<O> \<Longrightarrow> \<ominus>\<^bsub>K\<^esub> x \<in> carrier \<O>"
    proof-
      assume A: "x \<in> carrier \<O>"
      then have "\<nu> (\<ominus>\<^bsub>K\<^esub> x) = \<nu> x"  
        by (simp add: val_ring_subset valued_ring.val_add_inv valued_ring_axioms) 
      from this show "\<ominus>\<^bsub>K\<^esub> x \<in> carrier \<O>"
        by (simp add: A val_ring_minus0) 
     qed
    qed
  have C3: "\<And>x y.\<lbrakk>x \<in> carrier \<O>; y \<in> carrier \<O>\<rbrakk> \<Longrightarrow> x \<oplus>\<^bsub>K\<^esub> y \<in> carrier \<O>"
  proof-
    fix x y
    show "\<lbrakk>x \<in> carrier \<O>; y \<in> carrier \<O>\<rbrakk> \<Longrightarrow> x \<oplus>\<^bsub>K\<^esub> y \<in> carrier \<O>"
    proof- 
      assume X:"x \<in> carrier \<O>"
      assume Y:"y \<in> carrier \<O>"
      show " x \<oplus>\<^bsub>K\<^esub> y \<in> carrier \<O>"
      proof- 
        from X have vX: " \<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x" 
          using \<open>carrier \<O> \<subseteq> carrier K\<close> in_val_ring_conv by blast 
        from Y have vY: " \<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> y" 
          using \<open>carrier \<O> \<subseteq> carrier K\<close> in_val_ring_conv by blast 
        have 0: "\<nu> x \<in> vals \<Gamma>"
          using X by (meson C0 subsetCE val_range)  
        have 1: "\<nu> y \<in> vals \<Gamma>" 
          using Y by (meson C0 subsetCE val_range) 
        have 2: "\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> Min\<^bsub>\<Gamma>\<^esub>  (\<nu> x) (\<nu> y)" 
            by (simp add: vX vY)
        have 3: "Min\<^bsub>\<Gamma>\<^esub> (\<nu> x) (\<nu> y)\<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x \<oplus>\<^bsub>K\<^esub> y)" 
          by (meson C0 X Y rev_subsetD ultrametric) 
        have 4: "\<nu> (x \<otimes>\<^bsub>add_monoid K\<^esub> y) \<in> vals \<Gamma>" 
          using X Y val_ring_subset val_sum by auto 
        from 0 1 have 5:"Min\<^bsub>\<Gamma>\<^esub> (\<nu> x) (\<nu> y)\<in> carrier \<Gamma> \<union> {\<infinity>\<^bsub>\<Gamma>\<^esub>}"  by simp
        have 6: "\<one>\<^bsub>\<Gamma>\<^esub> \<in> vals \<Gamma>" 
          using one_is_val by auto 
        from 5 have 7: "Min\<^bsub>\<Gamma>\<^esub> (\<nu> x) (\<nu> y) \<in> carrier Order\<^bsub>\<Gamma>\<^esub>" by auto
        from 4 have 8: "\<nu> (x \<oplus>\<^bsub>K\<^esub> y) \<in> carrier Order\<^bsub>\<Gamma>\<^esub>" by auto
        have 9: "\<one>\<^bsub>\<Gamma>\<^esub> \<in> carrier Order\<^bsub>\<Gamma>\<^esub>" using "6" by auto
        have 10: "weak_partial_order Order\<^bsub>\<Gamma>\<^esub>" 
          using a_val_group extended_ordered_abelian_group.EOAG_is_pOrdered
                partial_order.axioms(1) by blast 
        have 11: "\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> (Min\<^bsub>\<Gamma>\<^esub> (\<nu> x) (\<nu> y))" 
          by (simp add: "2")
        have 12 :"Min\<^bsub>\<Gamma>\<^esub> (\<nu> x) (\<nu> y) \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x \<oplus>\<^bsub>K\<^esub> y)" 
          using "3" by auto
        have "gorder.le Order\<^bsub>\<Gamma>\<^esub> = le \<Gamma>" by auto 
        then have " \<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x \<otimes>\<^bsub>add_monoid K\<^esub> y)" 
          using 10 11 12 9 7 8 weak_partial_order.le_trans 
          by (smt monoid.select_convs(1))
        then show  " x \<oplus>\<^bsub>K\<^esub> y \<in> carrier \<O>" 
          by (simp add: X Y a_domain cring.cring_simprules(1)
              domain.axioms(1) val_ring_subset
              valued_ring.in_val_ring valued_ring_axioms) 
      qed
    qed
  qed

  have C4: "\<And>x y. \<lbrakk>x \<in> carrier \<O>; y \<in> carrier \<O>\<rbrakk> \<Longrightarrow> x \<otimes>\<^bsub>K\<^esub> y \<in> carrier \<O>"
  proof- fix x y
    show " \<lbrakk>x \<in> carrier \<O>; y \<in> carrier \<O>\<rbrakk> \<Longrightarrow> x \<otimes>\<^bsub>K\<^esub> y \<in> carrier \<O>"
    proof-
      assume A:"x \<in> carrier \<O>"
      assume B:"y \<in> carrier \<O>"
      show "x \<otimes>\<^bsub>K\<^esub> y \<in> carrier \<O>"
      proof-
        from A have  " \<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x" 
          by (simp add: valuation_ring_def)
        from B have  " \<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> y" 
         by (simp add: valuation_ring_def)
        from A have C: "\<nu> x \<in> vals \<Gamma>" 
          by (meson val_range valued_ring.val_ring_subset valued_ring_axioms) 
        have D: "\<nu> y \<in> vals \<Gamma>" 
          by (meson B valued_ring.val_range valued_ring.val_ring_subset valued_ring_axioms) 
        then  have G: "\<one>\<^bsub>\<Gamma>\<^esub>  \<otimes>\<^bsub>\<Gamma>\<^esub> \<one>\<^bsub>\<Gamma>\<^esub>  \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x \<otimes>\<^bsub>\<Gamma>\<^esub> \<nu> y"
          using C D extended_ordered_abelian_group.E_le_resp_mult2
          by (metis \<open>\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x\<close> \<open>\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> y\<close> a_val_group one_is_val) 
        from this have " \<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x \<otimes>\<^bsub>\<Gamma>\<^esub> \<nu> y" 
          using \<open>\<one>\<^bsub>K\<^esub> \<in> carrier K\<close> a_domain cring.cring_simprules(12)
                domain.axioms(1) val_one valued_ring.multiplicative
                valued_ring_axioms by force 
        from this and multiplicative have " \<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x \<otimes>\<^bsub>K\<^esub> y )"
          using A B val_ring_subset by auto 
        from this show "x \<otimes>\<^bsub>K\<^esub> y \<in> carrier \<O>" 
          by (simp add: A B a_domain cring.cring_simprules(5)
                domain.axioms(1) val_ring_subset valued_ring.in_val_ring valued_ring_axioms) 
      qed
    qed
  qed
  have C: "Ring.ring K" by (simp add: a_domain cring.axioms(1) domain.axioms(1)) 
  from C C0 C1 C2 C3 C4 show "subring (carrier \<O>) (K)" 
    by (simp add: ring.subringI)
qed

lemma (in valued_ring) val_ring_subcring:
  "subcring (carrier (valuation_ring G)) (ring G)"
    by (simp add: a_domain cring.subcringI' domain.axioms(1) val_ring_subring)

lemma (in valued_ring) val_ring_domain:
  "Ring.domain (valuation_ring G)"
proof-
  have 0:"domain (ring G)" by (simp add: a_domain)
  have 1:"(valuation_ring G) =  ((ring G)\<lparr>carrier := carrier (valuation_ring G)\<rparr>)" 
    by (simp add: valuation_ring_def)
  from 0 1 val_ring_subcring domain.subring_is_domain show "Ring.domain (valuation_ring G)"
  using val_ring_subring by fastforce
qed

lemma (in valued_ring) val_ring_minus1:
  assumes "x \<in> carrier \<O>"
  assumes "y \<in> carrier \<O>"
  assumes "y \<oplus>\<^bsub>\<O>\<^esub> x = \<zero>\<^bsub>\<O>\<^esub>" 
  shows "y =  \<ominus>\<^bsub>\<O>\<^esub> x"
proof-
  have "comm_group (add_monoid K)" 
    using Ring.ring_def a_domain abelian_group.a_comm_group cring_def domain.axioms(1) by blast
  from val_ring_domain have 0:"comm_group (add_monoid \<O>)" 
    using Ring.ring_def abelian_group.a_comm_group
          cring_def domain.axioms(1) by blast
  have 1:  "x \<in> carrier (add_monoid \<O>)"
    by (simp add: assms(1))
  have 2:  "y \<in> carrier (add_monoid \<O>)"
    by (simp add: assms(2))
  show  "y = \<ominus>\<^bsub>\<O>\<^esub> x" 
    using 0 1 2 assms(3) abelian_group.minus_equality comm_group_abelian_groupI by fastforce 
qed

lemma (in valued_ring) val_ring_minus2:
"x \<in> carrier \<O>\<Longrightarrow> \<ominus>\<^bsub>K\<^esub> x =  \<ominus>\<^bsub>\<O>\<^esub> x"
proof-
  assume X: " x \<in> carrier \<O>"
  show "\<ominus>\<^bsub>K\<^esub> x =  \<ominus>\<^bsub>\<O>\<^esub> x"
  proof-
    from X have P:"\<ominus>\<^bsub>K\<^esub> x \<in> carrier \<O>" using val_ring_minus0 by auto
    from this have "\<ominus>\<^bsub>K\<^esub> x \<oplus>\<^bsub>\<O>\<^esub> x = \<zero>\<^bsub>\<O>\<^esub>" 
    by (metis (no_types, lifting) 
        X a_domain cring.cring_simprules(9)
        domain.axioms(1) ring.simps(1) 
        ring_record_simps(12) valuation_ring_def
        valued_ring.val_ring_subset valued_ring_axioms) 
    from this and P show "\<ominus>\<^bsub>K\<^esub> x =  \<ominus>\<^bsub>\<O>\<^esub> x" 
      using X val_ring_minus1 by blast 
 qed
qed

lemma (in valued_ring) maximal_ideal_in_val_ring:
  "\<mm> \<subseteq> carrier \<O>"
proof
  fix x
  show "x \<in> \<mm> \<Longrightarrow> x \<in> carrier \<O>"
  by (simp add: maximal_ideal_def valued_ring.in_val_ring valued_ring_axioms)
qed

lemma (in valued_ring) maximal_ideal_is_ideal:
  "Ideal.ideal (maximal_ideal G) (valuation_ring G)"
proof-
  have I1: "subgroup \<mm> (add_monoid \<O>)"
  proof   
    show "\<mm> \<subseteq> carrier (add_monoid \<O>)"
      using maximal_ideal_def valued_ring.in_val_ring valued_ring_axioms by fastforce
    show "\<one>\<^bsub>add_monoid \<O>\<^esub> \<in> \<mm>"
    proof-
      have "\<one>\<^bsub>add_monoid (valuation_ring G)\<^esub> = \<zero>\<^bsub>(valuation_ring G)\<^esub>"  by simp
      from this have "\<one>\<^bsub>add_monoid (valuation_ring G)\<^esub> = \<zero>\<^bsub>K\<^esub>"
        by (simp add: valuation_ring_def)
      from this and val_zero have "\<nu> (\<one>\<^bsub>add_monoid (valuation_ring G)\<^esub>) = \<infinity>\<^bsub>\<Gamma>\<^esub>" by simp
      from group.Units have "\<one>\<^bsub>\<Gamma>\<^esub> \<in> carrier \<Gamma>"
        by (simp add: a_val_group 
            extended_ordered_abelian_group.axioms(1) ordered_abelian_group.one_in)
      from this  have  "\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<infinity>\<^bsub>\<Gamma>\<^esub> "
        by (simp add: extended_ordered_abelian_group.infinity_max1 a_val_group)
      from this show "\<one>\<^bsub>add_monoid (valuation_ring G)\<^esub> \<in> maximal_ideal G"
        using \<open>\<nu> \<one>\<^bsub>add_monoid (valuation_ring G)\<^esub> = \<infinity>\<^bsub>\<Gamma>\<^esub>\<close> \<open>\<one>\<^bsub>\<Gamma>\<^esub> \<in> carrier \<Gamma>\<close>
          \<open>\<one>\<^bsub>add_monoid (valuation_ring G)\<^esub> = \<zero>\<^bsub>K\<^esub>\<close> a_val_group 
          extended_ordered_abelian_group.infinity_max2 maximal_ideal_def
          subringE(1) subringE(2) val_ring_subring by fastforce
    qed
    show "\<And>x y. \<lbrakk>x \<in> \<mm>; y \<in> \<mm>\<rbrakk> \<Longrightarrow> x \<otimes>\<^bsub>add_monoid \<O>\<^esub> y \<in> \<mm>"
      proof-
        fix x y
        show " \<lbrakk>x \<in> \<mm>; y \<in> \<mm>\<rbrakk> \<Longrightarrow> x \<otimes>\<^bsub>add_monoid \<O>\<^esub> y \<in> \<mm>"
        proof-
          assume A: "x \<in> \<mm>"
          assume B: "y \<in> \<mm>"
          show "x \<otimes>\<^bsub>add_monoid \<O>\<^esub> y \<in> \<mm> "
          proof-
            from A have A0:"\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x" by (simp add: maximal_ideal_def)
            from B have B0:"\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> y" by (simp add: maximal_ideal_def)
            from A have A1:"\<one>\<^bsub>\<Gamma>\<^esub> \<noteq> \<nu> x" by (simp add: maximal_ideal_def)
            from B have B1:"\<one>\<^bsub>\<Gamma>\<^esub> \<noteq> \<nu> y" by (simp add: maximal_ideal_def)
            from A have A2:"x \<in> carrier K" by (simp add: maximal_ideal_def)
            from B have B2:"y \<in> carrier K" by (simp add: maximal_ideal_def)
            have MinC: " Extended_OAG.Min \<Gamma> (\<nu> x) (\<nu> y) \<in> carrier \<Gamma> \<union> {\<infinity>\<^bsub>\<Gamma>\<^esub>}" 
              using A2 B2 nonzero_val val_zero by auto
            have SumC: "\<nu> (x \<oplus>\<^bsub>K\<^esub> y) \<in> carrier \<Gamma> \<union> {\<infinity>\<^bsub>\<Gamma>\<^esub>}"
              using A2 B2 val_sum by auto
            have OneC: " \<one>\<^bsub>\<Gamma>\<^esub> \<in> carrier \<Gamma> \<union> {\<infinity>\<^bsub>\<Gamma>\<^esub>}" 
              using ordered_abelian_group.one_in 
              by (simp add: ordered_abelian_group.one_in 
                  a_val_group extended_ordered_abelian_group.axioms(1))
            have P: "\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> Extended_OAG.Min \<Gamma>  (\<nu> x) (\<nu> y)"  by (simp add: A0 B0)
            from this and ultrametric have Q:"Extended_OAG.Min \<Gamma> (\<nu> x) (\<nu> y) \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x \<oplus>\<^bsub>K\<^esub> y)" 
              using A2 B2 by blast
            have R: "\<one>\<^bsub>\<Gamma>\<^esub> \<noteq>Extended_OAG.Min \<Gamma> (\<nu> x) (\<nu> y)" 
              using ultrametric A1 B1 extended_ordered_abelian_group.EOAG_is_pOrdered by simp
            have X: "\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x \<oplus>\<^bsub>K\<^esub> y)"
              using P Q extended_ordered_abelian_group.EOAG_is_pOrdered weak_partial_order.le_trans 
              by (simp add: A0 A2 B0 B2 a_domain cring.cring_simprules(1) domain.axioms(1) 
                  subringE(7) val_ring_subring valued_ring.in_val_ring 
                  valued_ring.in_val_ring_conv valued_ring_axioms)
            from this have " \<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x \<otimes>\<^bsub>add_monoid (valuation_ring G)\<^esub> y)" 
                by (simp add: valuation_ring_def)
              have  "\<one>\<^bsub>\<Gamma>\<^esub> \<noteq> \<nu> (x \<oplus>\<^bsub>K\<^esub> y)" 
                using  OneC MinC SumC  P Q R   extended_ordered_abelian_group.chain 
                by (smt a_val_group)
            from this and X show "x \<otimes>\<^bsub>add_monoid (valuation_ring G)\<^esub> y \<in> maximal_ideal G " 
              by (simp add: A2 B2 a_domain cring.cring_simprules(1) 
                  domain.axioms(1) maximal_ideal_def valuation_ring_def)
          qed
        qed
      qed
    show "\<And>x. x \<in> \<mm> \<Longrightarrow> inv\<^bsub>add_monoid \<O>\<^esub> x \<in> \<mm>"
    proof-
      fix x
      show " x \<in> \<mm> \<Longrightarrow> inv\<^bsub>add_monoid \<O>\<^esub> x \<in> \<mm>"
      proof-
        assume A: " x \<in> \<mm>"
        show "inv\<^bsub>add_monoid \<O>\<^esub> x \<in> \<mm>"
        proof-
          from A have Q0: "\<nu> (\<ominus>\<^bsub>K\<^esub> x) = \<nu> x" 
            using maximal_ideal_def valued_ring.val_add_inv valued_ring_axioms by fastforce
          from val_ring_subcring A have "\<ominus>\<^bsub>\<O>\<^esub> x = \<ominus>\<^bsub>K\<^esub> x" 
            by (metis  maximal_ideal_in_val_ring subset_iff val_ring_minus2) 
          from this and valuation_ring_def have P:"\<nu> (\<ominus>\<^bsub>\<O>\<^esub> x) = \<nu> x"
            using Q0 by auto 
          from this have Q1: " \<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub>\<nu> (inv\<^bsub>add_monoid (valuation_ring G)\<^esub> x)" 
            using A maximal_ideal_def by (simp add: maximal_ideal_def a_inv_def) 
          from P have Q2: " \<one>\<^bsub>\<Gamma>\<^esub> \<noteq> \<nu> (inv\<^bsub>add_monoid (valuation_ring G)\<^esub> x)"
            using A by (simp add: maximal_ideal_def a_inv_def) 
          have Q3: "inv\<^bsub>add_monoid (valuation_ring G)\<^esub> x \<in> carrier K" 
            by (metis (no_types, lifting) A \<open>\<ominus>\<^bsub>\<O>\<^esub> x = \<ominus>\<^bsub>K\<^esub> x\<close> a_domain a_inv_def 
                cring.cring_simprules(3) domain.axioms(1)
                maximal_ideal_def mem_Collect_eq partial_object_ext_def) 
          show "inv\<^bsub>add_monoid (valuation_ring G)\<^esub> x \<in> maximal_ideal G" 
            using Q1 Q2 Q3 maximal_ideal_def  by (simp add: maximal_ideal_def)
        qed
      qed
    qed
  qed
  have I2:"\<And>a x. \<lbrakk>a \<in> \<mm>; x \<in> carrier \<O>\<rbrakk> \<Longrightarrow> x \<otimes>\<^bsub>\<O>\<^esub> a \<in> \<mm>"
  proof-
    fix a x
    show "\<lbrakk>a \<in> \<mm> ; x \<in> carrier \<O>\<rbrakk> \<Longrightarrow> x \<otimes>\<^bsub>\<O>\<^esub> a \<in> \<mm>"
    proof-
      assume 0: "a \<in> \<mm>"
      assume 1: "x \<in> carrier \<O>"
      show "x \<otimes>\<^bsub>\<O>\<^esub> a \<in> \<mm>"
      proof-
        from 1 have C1:"\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x" by (simp add: valuation_ring_def)
        from 0 have C2:"\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> a" by (simp add: maximal_ideal_def)
        from 0 have C3:"\<one>\<^bsub>\<Gamma>\<^esub> \<noteq> \<nu> a" by (simp add: maximal_ideal_def)
        from C1 C2 C3 0 1 have "\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x \<otimes>\<^bsub>valuation_ring G\<^esub> a)" 
          by (meson cring.cring_simprules(5) domain.axioms(1) 
              maximal_ideal_in_val_ring subringE(1) subsetCE val_ring_domain
              val_ring_subring valued_ring.in_val_ring_conv valued_ring_axioms) 
        from 1 have C4: " \<nu> x \<in> vals \<Gamma>" 
          by (metis UnI1 UnI2 singletonI subringE(1) subsetCE val_ring_subring 
              val_zero valued_ring.nonzero_val valued_ring_axioms)
        from 0 have C5: " \<nu> a \<in> vals \<Gamma>" 
          by (meson maximal_ideal_in_val_ring subringE(1) subsetCE
              val_ring_subring valued_ring.val_range valued_ring_axioms) 
        from C1 C2 C3 0  1 have C6: "\<nu> a \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x \<otimes>\<^bsub>K\<^esub> a)"
          by (simp add: maximal_ideal_def prod_inequality valuation_ring_def)
        have "\<one>\<^bsub>\<Gamma>\<^esub> \<noteq> \<nu> (x \<otimes>\<^bsub>valuation_ring G\<^esub> a)"
        proof -
          have "\<not> \<nu> a \<preceq>\<^bsub>\<Gamma>\<^esub> \<one>\<^bsub>\<Gamma>\<^esub>"
            by (meson C2 C3 C5 a_val_group extended_ordered_abelian_group.anti_symm one_is_val)
          then show ?thesis
            by (metis (no_types) C6 monoid.select_convs(1) valuation_ring_def)
        qed 
        from this show "x \<otimes>\<^bsub>\<O>\<^esub> a \<in> \<mm>"
          by (metis (mono_tags, lifting) "0" "1" CollectI \<open>\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> (x \<otimes>\<^bsub>\<O>\<^esub> a)\<close> 
              cring.cring_simprules(5) domain.axioms(1) maximal_ideal_def 
              maximal_ideal_in_val_ring subringE(1) subsetCE val_ring_domain val_ring_subring) 
      qed
    qed
  qed 
  have I3:"\<And>a x. \<lbrakk>a \<in> \<mm>; x \<in> carrier \<O>\<rbrakk> \<Longrightarrow> a \<otimes>\<^bsub>\<O>\<^esub> x \<in> \<mm>"
  proof-
    fix a x
    show "\<lbrakk>a \<in> \<mm>; x \<in> carrier \<O>\<rbrakk> \<Longrightarrow> a \<otimes>\<^bsub>\<O>\<^esub> x \<in> \<mm>"
    proof-
      assume A1: "a \<in> \<mm>"
      assume A2: "x \<in> carrier \<O>"
      show "a \<otimes>\<^bsub>\<O>\<^esub> x \<in> \<mm>" using A1 A2 I2 
        by (metis (no_types, lifting) cring.cring_simprules(14) 
            domain.axioms(1) maximal_ideal_in_val_ring subsetCE val_ring_domain) 
    qed
  qed
  from I1 I2 I3 idealI show ?thesis 
    using cring_def domain.axioms(1) val_ring_domain by blast 
qed

lemma (in valued_field) maximal_ideal_maximal:
  "maximalideal \<mm> \<O>"
proof(rule maximalidealI)
  show "ideal \<mm> \<O>" 
    by (simp add: maximal_ideal_is_ideal)
  show "carrier \<O> \<noteq> \<mm>" 
    by (metis (mono_tags, lifting) maximal_ideal_def
        mem_Collect_eq subringE(3) val_one val_ring_subring)
  show "\<And>J. ideal J \<O> \<Longrightarrow> \<mm> \<subseteq> J \<Longrightarrow> J \<subseteq> carrier \<O> \<Longrightarrow> J = \<mm> \<or> J = carrier \<O> "
  proof-
    fix J
    assume 0: "ideal J \<O>"
    assume 1: "\<mm> \<subseteq> J"
    assume 2: "J \<subseteq> carrier \<O>"
    show "(J = \<mm> \<or> (J = carrier \<O>))"
    proof (cases "J = \<mm>")
      case True
        then  show "(J = \<mm> \<or> (J = carrier \<O>))" by auto
      next
      case False
        from False and 1  have "\<exists> x. x \<in> J \<and> x \<notin> \<mm>"  by blast
        from this obtain x where C0: " x \<in> J \<and> x \<notin> \<mm>" by auto
        from 2 have "\<one>\<^bsub>\<Gamma>\<^esub> \<preceq>\<^bsub>\<Gamma>\<^esub> \<nu> x"
          by (meson C0 subringE(1) subsetCE val_ring_subring
              valued_ring.in_val_ring_conv valued_ring_axioms)
        from this and C0 have C1: "\<one>\<^bsub>\<Gamma>\<^esub> =  \<nu> x"
          using "2" maximal_ideal_def subringE(1) val_ring_subring by fastforce
        have C2: "x \<in> carrier K"
          by (meson "2" C0 subringE(1) subsetCE val_ring_subring)
        from C1 C2 val_ring_units have "x \<in> Units \<O>" 
          using "2" C0 by auto
        from this and Units_def have "\<exists> y  \<in> carrier \<O>. y \<otimes>\<^bsub>\<O>\<^esub> x = \<one>\<^bsub>\<O>\<^esub> \<and>  x \<otimes>\<^bsub>\<O>\<^esub> y = \<one>\<^bsub>\<O>\<^esub>" 
          by (simp add: Units_def)
        from this obtain y where 
        "y  \<in> carrier \<O>\<and> y \<otimes>\<^bsub>\<O>\<^esub> x = \<one>\<^bsub>\<O>\<^esub> \<and>  x \<otimes>\<^bsub>\<O>\<^esub> y = \<one>\<^bsub>\<O>\<^esub>" by auto
        from this C0 and 0 have "\<one>\<^bsub>\<O>\<^esub> \<in> J" using ideal.I_r_closed by fastforce
        from this and 0 have "J =  carrier \<O>" 
          using ideal.one_imp_carrier by blast
        then  show "(J = \<mm> \<or> (J = carrier \<O>))" by auto
      qed
    qed
  qed

lemma (in valued_field) res_field_is_field:
  "Ring.field k"
proof-
  show  "Ring.field k"
    using maximal_ideal_maximal  val_ring_subring residue_field_def 
    by (simp add: residue_field_def domain.axioms(1) maximalideal.quotient_is_field val_ring_domain)
qed


end

