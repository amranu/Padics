theory pochhammer_monomials
  imports "~~/src/HOL/Computational_Algebra/Formal_Power_Series"  
          "~~/src/HOL/Computational_Algebra/Polynomial"  
          "~~/src/HOL/Computational_Algebra/Polynomial_FPS"
begin

(************************************Leading term function*****************************************)

abbreviation "X \<equiv> [:0,1:]"

definition leading_term:: "'a::zero poly \<Rightarrow> 'a poly" where
"leading_term p \<equiv> monom (lead_coeff p) (degree p)"

lemma leading_term_idem:
"leading_term (leading_term p) = leading_term p"
  by (metis (no_types, lifting)
      degree_monom_eq lead_coeff_monom 
      leading_term_def monom_eq_iff') 

lemma leading_term_degree:
"degree p = degree (leading_term p)"
  by (metis degree_monom_eq lead_coeff_monom leading_coeff_0_iff leading_term_def) 

lemma leading_term_lead_coeff:
"lead_coeff p = lead_coeff (leading_term p)"
  by (metis lead_coeff_monom leading_term_def) 

lemma minus_leading_term:
  assumes "degree p >0"
  shows "degree (p - (leading_term p))< degree p"
proof-
  let ?n = "degree p"
  let ?q = "p - (leading_term p)"
  show "degree ?q < ?n"
  proof-
    have M: "max (degree p) (degree (leading_term p)) = ?n"
      using leading_term_degree by (metis max.idem) 
    then have  "degree ?q \<le> max (degree p) (degree (leading_term p))" using degree_diff_le_max 
    proof -
    { assume "0 \<noteq> p \<and> p - leading_term p \<noteq> 0"
      moreover
      { assume "0 - coeff (leading_term p) (degree (p - leading_term p)) = 0 \<and> p - leading_term p \<noteq> 0"
        then have "degree (p - leading_term p) \<le> degree p"
          by (metis le_degree leading_coeff_0_iff minus_poly.rep_eq) }
      ultimately have "degree (p - leading_term p) \<le> degree p"
      by (metis (no_types) cancel_comm_monoid_add_class.diff_cancel le_degree leading_term_degree) }
  then show ?thesis
    by (metis (no_types) assms degree_0 leading_term_degree linear max.idem not_le)
    qed 
    then have le:  "degree ?q \<le> ?n" 
      using M  by simp 
    have "coeff ?q ?n = 0" 
      by (simp add: leading_term_def)
    then have "degree ?q \<noteq> ?n"
      by (metis assms degree_0 le leading_coeff_neq_0 not_le) 
    then show ?thesis using le by simp
  qed
qed

lemma leading_term_eq_deg_less:
  assumes "degree p1 > 0"
  assumes "leading_term p1 = leading_term p2"
  shows "degree (p1 - p2) < degree p1"
proof-
  let ?q = "p1 - p2"
  let ?n = "degree p1"
  have "degree p2 = ?n" 
    using assms(2) leading_term_degree by metis 
  then have "coeff ?q ?n = 0"
    by (metis assms(2) cancel_comm_monoid_add_class.diff_cancel coeff_diff leading_term_lead_coeff) 
  then show "degree ?q < ?n" 
    by (smt One_nat_def Suc_le_eq Suc_pred
        \<open>degree p2 = degree p1\<close> assms(1)
        coeff_0_degree_minus_1 coeff_diff
        degree_0 le_degree leading_coeff_0_iff not_le) 
qed

lemma leading_term_decomp:
  assumes "degree (p::('a::comm_ring_1) poly) >0"
  obtains q where "p = q + (leading_term p)" and "degree q < degree p"
proof-
  let ?q = "p - (leading_term p)"
  let ?n = "degree p"
  have 0:"degree ?q < ?n" 
    using minus_leading_term assms by blast 
  have 1:"p = ?q + (leading_term p)" by simp
  then show ?thesis 
    using 0 1 that by blast 
qed


lemma leading_term_mult:
  assumes "(a ::'a::comm_ring_1)*b \<noteq>0"
  assumes "a = lead_coeff p"
  assumes "b = lead_coeff q"
  assumes "degree p > 0"
  assumes "degree q >0"
  shows "leading_term (p*q) = (leading_term p)*(leading_term q)"
proof-
  obtain p1 where "p = leading_term p + p1" and "degree p1 < degree p"
    using leading_term_decomp  by (metis add.commute assms(4)) 
  obtain q1 where "q = leading_term q + q1" and "degree q1 < degree q"
    using leading_term_decomp  by (metis add.commute assms(5))
  then have "p*q = (leading_term p)*(leading_term q) + p1*(leading_term q) + q1*(leading_term p) + p1*q1"
    by (metis \<open>p = leading_term p + p1\<close> add.assoc mult.commute ring_class.ring_distribs(1)) 
  then have "p*q = (monom a (degree p))*(monom b (degree q)) + p1*(leading_term q) + q1*(leading_term p) + p1*q1"
    by (simp add: assms(2) assms(3) leading_term_def)
  then have "p*q = (monom (a*b) ((degree p)+(degree q))) + p1*(leading_term q) + q1*(leading_term p) + p1*q1"
    by (simp add: mult_monom)
  then show ?thesis 
    by (metis (no_types, lifting) assms(1)
        assms(2) assms(3) coeff_mult_degree_sum
        degree_mult_le le_degree leading_term_def
        mult_monom order_antisym) 
qed

lemma times_X_degree:
  assumes "(p::('a::comm_ring_1) poly) \<noteq>0"
  shows "degree (X*p) = (Suc (degree p))"
  by (simp add: assms) 

lemma leading_term_mult_X:
  assumes "degree (p::('a::comm_ring_1) poly) \<noteq>0"
  shows "leading_term (X*p) = X*(leading_term p)"
proof-
  have "leading_term (X*p) = leading_term (X*(leading_term p))"
  proof -
    have "\<forall>p. degree p = degree (monom (lead_coeff p::'a) (degree p))"
      by (metis leading_term_def leading_term_degree)
    then show ?thesis
      by (simp add: leading_term_def)
  qed
  have "leading_term(X*(leading_term p)) = X*leading_term p"
    by (metis (no_types, lifting) assms coeff_pCons_Suc
      degree_0 leading_term_def leading_term_degree 
      leading_term_lead_coeff monom_Suc mult.commute
      mult.right_neutral mult_pCons_left one_pCons smult_0_left times_X_degree) 
  then show ?thesis 
    using \<open>leading_term (X * p) = leading_term (X * leading_term p)\<close> by auto 
qed

lemma leading_term_sum:
  assumes "degree p0 = degree p1"
  assumes "degree q < degree p0"
  assumes "p0 = p1 + q"
  shows "leading_term p0 = leading_term p1"
  by (metis add.commute assms(1) assms(2) 
      assms(3) lead_coeff_add_le leading_term_def) 

lemma monom_leading_term_monic_lin_comp0:
  assumes "b \<noteq>0"
  assumes A: "degree a = 0"
  shows "leading_term ((monom b n) \<circ>\<^sub>p (X + a)) = leading_term ((monom b n)::('a::comm_ring_1) poly)"
proof(induction n)
  case 0 
  then show ?case by (simp add: monom_0) 
next 
  case (Suc n)
  fix n
  assume IH: "leading_term (monom b n \<circ>\<^sub>p (X + a)) = leading_term (monom b n)"
  show "leading_term (monom b (Suc n) \<circ>\<^sub>p (X + a)) = leading_term (monom b (Suc n)) "
  proof-
    have 0: "(monom b (Suc n)) =(monom b n)* (monom 1 1)"
       by (simp add: mult_monom) 
    then have "(monom b (Suc n))\<circ>\<^sub>p(X + a) =(monom b n) \<circ>\<^sub>p(X + a)* (monom 1 1) \<circ>\<^sub>p(X+ a)"
      by (simp add: pcompose_mult) 
    then have "(monom b (Suc n))\<circ>\<^sub>p(X + a) = (monom b n) \<circ>\<^sub>p(X+ a)*(X + a)"
      by (simp add: monom_Suc mult.commute pcompose_pCons) 
    then have Q: "(monom b (Suc n))\<circ>\<^sub>p(X + a) = X*(monom b n) \<circ>\<^sub>p(X+ a) + a*(monom b n) \<circ>\<^sub>p(X+ a)"
      by (simp add: mult.commute mult_poly_add_left) 
    have "((monom b n) \<circ>\<^sub>p(X+ a)) \<noteq>0"
      by (metis IH assms(1) lead_coeff_monom leading_coeff_0_iff leading_term_def) 
    then have R: "degree (X*(monom b n) \<circ>\<^sub>p(X+ a)) = 1+  degree  ((monom b n) \<circ>\<^sub>p(X+ a))"
      by simp 
    then have S: " degree ((monom b (Suc n))\<circ>\<^sub>p(X + a)) =  degree (X*(monom b n) \<circ>\<^sub>p(X+ a))"
      using Q by (smt A One_nat_def add.commute add_Suc comm_monoid_mult_class.mult_1
        degree_add_eq_left degree_mult_le degree_of_nat leading_term_degree
        leading_term_sum linorder_neqE_nat linorder_not_le not_less_eq_eq
        of_nat_1 one_poly_eq_simps(2) plus_1_eq_Suc) 
    have "degree  ((monom b n) \<circ>\<^sub>p(X+ a)) \<ge> degree  (a*(monom b n) \<circ>\<^sub>p(X+ a))"
      using A degree_mult_le by (metis One_nat_def add_Suc
                        not_less_eq_eq plus_1_eq_Suc)
    then have T: "degree (X*(monom b n) \<circ>\<^sub>p(X+ a)) >  degree  (a*(monom b n) \<circ>\<^sub>p(X+ a))"
      using R by linarith 
    let ?p0 = "(monom b (Suc n))\<circ>\<^sub>p(X + a) "
    let ?p1 = "(X*(monom b n) \<circ>\<^sub>p(X+ a))"
    let ?q = "(a*(monom b n) \<circ>\<^sub>p(X+ a))"
    have P0: "degree ?p0 = degree ?p1" using S by auto
    have P1: "degree ?q < degree ?p1" using T by auto
    have P2: "?p0 = ?p1 + ?q" using Q by auto
    have "leading_term ?p0 = leading_term ?p1"
      using P0 P1 P2 leading_term_sum by (simp add: leading_term_sum) 
    then show ?thesis
      using IH by (metis (no_types, lifting) One_nat_def R 0 assms(1)
          coeff_mult_degree_sum degree_monom_eq lead_coeff_monom
          leading_term_def monom_Suc monom_eq_1 mult.commute 
          one_neq_zero one_pCons plus_1_eq_Suc)
  qed
qed

lemma monom_leading_term_monic_lin_comp:
  assumes "b \<noteq>0"
  assumes A: "degree a = 0"
  shows "leading_term ((monom b n) \<circ>\<^sub>p (X + a)) = ((monom b n)::('a::comm_ring_1) poly)"
  using monom_leading_term_monic_lin_comp0 
  by (metis A assms(1) degree_monom_eq lead_coeff_monom leading_term_def) 

lemma comp_lin_degree:
  assumes A: "degree (a::('a::comm_ring_1) poly) = 0"
  shows "degree (p \<circ>\<^sub>p (X + a)) = degree p"
proof(cases "degree p = 0")
  case True
  then show ?thesis 
    by (metis degree_eq_zeroE pcompose_const) 
next
  case False 
  let ?q = "p - (leading_term p)"
  have "degree ?q < degree p"
    using False minus_leading_term by auto 
  have LE:"degree (?q \<circ>\<^sub>p (X+a)) \<le>degree ?q"
    using A by (metis (mono_tags, lifting) 
        One_nat_def degree_add_eq_left degree_pCons_eq_if
        degree_pcompose_le mult.right_neutral 
        one_neq_zero one_pCons zero_less_one) 
  obtain b where I:"leading_term p = monom b (degree p)"
     by (simp add: leading_term_def) 
  have N: "b \<noteq>0"
     using False by (metis I degree_0 
         leading_term_degree monom_eq_0_iff) 
  let ?m = "(monom b (degree p))" 
  have B: "leading_term (?m \<circ>\<^sub>p(X + a)) = ?m"
    using A N monom_leading_term_monic_lin_comp by auto
  have "leading_term p = ?m"
    by (simp add: I) 
  have P0: "degree ?m = degree (?m \<circ>\<^sub>p (X + a))" 
    by (metis B leading_term_degree) 
  have "p \<circ>\<^sub>p (X + a) = (?m \<circ>\<^sub>p (X + a)) + (?q \<circ>\<^sub>p (X + a))"
    by (simp add: I pcompose_diff) 
  then have "degree (p \<circ>\<^sub>p (X + a)) = degree ?m" 
    using P0 LE by (metis (no_types, lifting) I 
      \<open>degree (p - leading_term p) < degree p\<close> 
      add_lessD1 degree_add_eq_left le_add_diff_inverse
      leading_term_degree) 
  then show ?thesis by (simp add: N degree_monom_eq) 
qed

lemma leading_term_monic_lin_comp:
  assumes "degree a = 0"
  shows "leading_term (p \<circ>\<^sub>p (X + a)) = leading_term (p::('a::comm_ring_1) poly)"
proof(cases "degree p = 0")
  case True
  then show ?thesis 
    by (metis degree_eq_zeroE pcompose_const) 
next 
  case False 
  obtain q where E: "p = q + (leading_term p)" and D: "degree q < degree p"
    using leading_term_decomp False by blast 
  then have P0: "leading_term ((leading_term p) \<circ>\<^sub>p (X + a)) = (leading_term p)"
    using monom_leading_term_monic_lin_comp by (metis (no_types, lifting)
        False assms degree_0 leading_coeff_0_iff leading_term_def) 
  have "p \<circ>\<^sub>p (X + a) = q \<circ>\<^sub>p (X + a) + (leading_term p) \<circ>\<^sub>p (X + a)" 
    using E by (metis pcompose_add)
  have P1: "degree (q \<circ>\<^sub>p (X + a)) < degree (p \<circ>\<^sub>p (X + a))"
    using D by (simp add: assms comp_lin_degree) 
  have "degree (p \<circ>\<^sub>p (X + a)) = degree p"
     by (simp add: assms comp_lin_degree) 
  then have "leading_term (p \<circ>\<^sub>p (X + a)) = leading_term ((leading_term p) \<circ>\<^sub>p (X + a))"
    by (smt D \<open>p \<circ>\<^sub>p (X + a) = q \<circ>\<^sub>p (X + a) + leading_term p \<circ>\<^sub>p (X + a)\<close>
        add.commute assms comp_lin_degree leading_term_degree
        leading_term_sum) 
  then show ?thesis using P0 by auto
qed

(**************************************Pochhammer monomial constructor*****************************)

fun pochhammer_monom:: "'a::comm_ring_1 \<Rightarrow> nat  \<Rightarrow> 'a::comm_ring_1 poly" ("PM _ _")  where
"pochhammer_monom a 0 = monom a 0"|
"pochhammer_monom a (Suc n) = (X - (of_nat n))*(pochhammer_monom a n)"

lemma pochhammer_monom_alt_def:
"pochhammer_monom a n = smult a (pochhammer (X - (of_nat n) + 1) n)"
proof(induction n)
  case 0
  then show ?case  by (simp add: monom_0) 
next
  case (Suc n)
  fix n 
  assume IH : " (PM a n) = smult a (pochhammer (X - of_nat n + 1) n)"
  show "(PM a (Suc n)) = smult a (pochhammer (X - (of_nat (Suc n)) + 1) (Suc n))"
  proof-
    have "(PM a (Suc n)) = (X - (of_nat n))*(PM a n)"
      by simp
    then have "(PM a (Suc n)) = (X - (of_nat n))* (smult a (pochhammer (X - of_nat n + 1) n))"
      by (simp add: IH) 
    then show ?thesis by (simp add: pochhammer_rec) 
  qed
qed

lemma pochhammer_zero_root:
  shows "poly (PM (a::('a::comm_ring_1)) (Suc n)) 0 = 0"
proof-
  let ?n = "Suc n"
  have "(pochhammer  ((X::'a poly) - (of_nat ?n) + 1) ?n) = (( (X - (of_nat ?n) + 1) + (of_nat n))* (pochhammer  (X - (of_nat ?n) + 1) n))"
    using pochhammer_rec'  by blast 
  then have "(pochhammer  ((X::'a poly) - (of_nat ?n) + 1) ?n) = X* (pochhammer  (X - (of_nat ?n) + 1) n)"
    by simp 
  then have  "(PM (a::('a::comm_ring_1)) (Suc n)) = smult a ( X* (pochhammer  (X - (of_nat ?n) + 1) n))"
    by (simp add: pochhammer_monom_alt_def) 
  then show ?thesis by simp 
qed

lemma pochhammer_roots:
"k < n \<Longrightarrow> poly (PM (a::('a::comm_ring_1)) n) (of_nat k) = 0"
proof(induction n)
  case 0
  then show ?case 
    by simp 
next
  case (Suc n)
  fix n
  assume IH0: "(k < n) \<Longrightarrow> poly (PM a n) (of_nat k) = 0"
  assume IH1: "k < Suc n"
  have "(PM a (Suc n)) = (X - (of_nat n))*(PM a n)"
    by simp 
  then show "poly (PM a (Suc n)) (of_nat k) = 0"
    using IH0 IH1 by (metis (no_types, lifting) diff_0
        diff_pCons diff_zero dvdI less_SucE mult_not_zero
        of_nat_poly poly_eq_0_iff_dvd poly_mult) 
qed

lemma pochhammer_eval_nat:
  assumes "(a::('a::{idom, ring_char_0})) \<noteq>0"
  shows "k \<ge> d \<Longrightarrow> poly (PM a d) (of_nat k) = a * (of_nat (k choose d))*(pochhammer 1 d)"
proof(induction d)
  case 0
  have "(PM a 0)= smult a 1"
    by (simp add: monom_0) 
  then show ?case 
    by simp 
next 
  case (Suc n)
  fix n
  assume IH0: "k \<ge> n\<Longrightarrow>poly (PM a n) (of_nat k) = a * (of_nat (k choose n))*(pochhammer 1 n)"
  assume IH1: "k \<ge> Suc n"
  have "(PM a (Suc n)) = (X - of_nat n)*(PM a n)"
    by simp  
  then have "poly (PM a (Suc n)) (of_nat k) = (poly (X - of_nat n) (of_nat k))* a * (of_nat (k choose n))*(pochhammer 1 n)"
    using IH0 IH1 by simp 
  then have "poly (PM a (Suc n)) (of_nat k) = ((of_nat k) - of_nat n)* a * (of_nat (k choose n))*(pochhammer 1 n)"
    by (simp add: of_nat_poly)
  then have "poly (PM a (Suc n)) (of_nat k) =  a * ((of_nat k) - of_nat n)*(of_nat (k choose n))*(pochhammer 1 n)"
    by simp 
  then have "poly (PM a (Suc n)) (of_nat k) =  a * (of_nat (k - n))*(of_nat (k choose n))*(pochhammer 1 n)"
    by (metis add_diff_cancel_left' binomial_eq_0
        le_add_diff_inverse linorder_not_le 
        mult_cancel_right of_nat_add of_nat_eq_0_iff)  
  then have "poly (PM a (Suc n)) (of_nat k) =  a * (of_nat ((k - n)*(k choose n)*(pochhammer 1 n)))"
    by (metis (no_types, lifting) mult.assoc
        of_nat_1 of_nat_mult pochhammer_of_nat) 
  then have "poly (PM a (Suc n)) (of_nat k) =  a *(of_nat (k choose (Suc n))*(pochhammer 1 (Suc n)))"
    by (smt binomial_absorb_comp binomial_absorption mult.assoc 
        mult.left_commute of_nat_1 of_nat_add of_nat_mult 
        plus_1_eq_Suc pochhammer_of_nat pochhammer_rec') 
  then show "poly (PM a (Suc n)) (of_nat k) = a * (of_nat (k choose Suc n)) *( pochhammer 1 (Suc n))"
    by simp  
qed



lemma pochhammer_monom_pcompose:
"pcompose (pochhammer_monom a n) p =  smult a (pochhammer (p - (of_nat n) + 1) n)"
proof(induction n)
  case 0
  then show ?case by (simp add: pochhammer_monom_alt_def) 
next
  case (Suc n)
  fix n
  assume IH: " (PM a n) \<circ>\<^sub>p p = smult a (pochhammer (p - of_nat n + 1) n)"
  show "(PM a (Suc n)) \<circ>\<^sub>p p = smult a (pochhammer (p - of_nat (Suc n) + 1) (Suc n))"
  proof-
    have  "(PM a (Suc n)) \<circ>\<^sub>p p = (X - (of_nat n)) \<circ>\<^sub>p p *(PM a n) \<circ>\<^sub>p p "
      by (simp add: pcompose_mult) 
    then have "(PM a (Suc n)) \<circ>\<^sub>p p = (p - (of_nat n)) *(PM a n) \<circ>\<^sub>p p "
      using pcompose_pCons by (metis (no_types, lifting) add_cancel_left_left
        mult.commute mult.left_neutral of_nat_poly 
        pCons_0_0 pCons_one pcompose_const pcompose_diff) 
    then show ?thesis 
      using IH pochhammer_monom_alt_def by (simp add: pochhammer_rec) 
  qed
qed

(*******************************Pochhammer monomials have the correct degree***********************)

lemma pochhammer_leading_term:
  assumes "a \<noteq>0"
  shows "leading_term (pochhammer_monom a n) = monom a n"
proof(induction n)
  case 0
  then show ?case 
    by (simp add: leading_term_def monom_0) 
next 
  case (Suc n)
  fix n
  assume IH: "leading_term (pochhammer_monom a n) = monom a n"
  show "leading_term (pochhammer_monom a (Suc n)) = monom a (Suc n)"
  proof-
    have P0:"pochhammer_monom a (Suc n) 
            = (X - (of_nat n))*(pochhammer_monom a n)" by simp
    then have P1: "pochhammer_monom a (Suc n) 
            = X*(pochhammer_monom a n) - (of_nat n)*(pochhammer_monom a n)"
      by (simp add: left_diff_distrib') 
    have "(pochhammer_monom a n) \<noteq>0" 
      by (metis IH assms coeff_diff degree_0 
          degree_monom_eq diff_numeral_special(9)
          lead_coeff_monom leading_term_lead_coeff
          monom_eq_1 one_neq_zero) 
    then have "degree (X*(monom a n)) > degree ((of_nat n)*(monom a n))"
      using degree_of_nat  by (metis add.left_neutral assms degree_mult_le
              degree_pCons_eq linorder_not_le monom_eq_0_iff
              mult.left_neutral mult_pCons_left not_less_eq_eq one_pCons smult_0_left)
    then have P2: "degree (X*(pochhammer_monom a n)) > degree ((of_nat n)*(pochhammer_monom a n))"
      using IH by (metis (no_types, lifting) add.left_neutral
                    degree_mult_le degree_of_nat degree_pCons_eq 
                    lead_coeff_monom  leading_term_def  linorder_not_le
                    monom_eq_0_iff mult.left_neutral mult_pCons_left
                    not_less_eq_eq  one_pCons smult_0_left)
    then have "degree (pochhammer_monom a (Suc n))  = degree (X*(pochhammer_monom a n))" 
      using P1 P2  by (smt IH P0 assms coeff_mult_degree_sum 
                    degree_mult_le degree_pCons_eq diff_pCons
                    diff_zero le_degree lead_coeff_1 lead_coeff_monom 
                    lead_coeff_pCons(1) leading_term_def mult.left_neutral 
                    of_nat_poly one_neq_zero one_pCons order_antisym) 
    then show ?thesis 
      by (smt IH P1 P2 add.left_neutral
        assms coeff_diff degree_monom_eq 
        degree_pCons_eq_if diff_zero le_degree
        lead_coeff_monom lead_coeff_pCons(1) 
        leading_term_def linorder_not_le
        mult.left_neutral mult_not_zero 
        mult_pCons_left one_pCons smult_0_left) 
  qed
qed

lemma pochhammer_monom_degree:
  assumes "a \<noteq>0"
  shows "degree (pochhammer_monom a n) = n"
  using pochhammer_leading_term leading_term_degree by (metis assms degree_monom_eq) 


(*****************************Pochhammer leading term function*************************************)

definition pochhammer_lt::"'a::comm_ring_1 poly \<Rightarrow> 'a poly" where 
"pochhammer_lt p \<equiv> pochhammer_monom (lead_coeff p) (degree p)"

lemma pochhammer_lt_degree:
"degree (pochhammer_lt p) = degree p" 
  by (metis  coeff_0_reflect_poly coeff_0_reflect_poly_0_iff
      degree_0 monom_eq_0 pochhammer_lt_def 
      pochhammer_monom.simps(1) pochhammer_monom_degree) 


lemma minus_pochhammer_leading_term:
  assumes "degree p >0"
  shows "degree (p - (pochhammer_lt p))< degree p"
proof-
  let ?n = "degree p"
  let ?q = "p - (pochhammer_lt p)"
  show "degree ?q < ?n"
  proof-
    have "leading_term p = leading_term ((pochhammer_lt p))"
      by (metis assms degree_0 leading_coeff_0_iff
        leading_term_def neq0_conv pochhammer_leading_term
        pochhammer_lt_def) 
    then show ?thesis by (simp add: assms leading_term_eq_deg_less) 
  qed
qed

lemma pochhammer_leading_term_decomp:
  assumes "degree (p::('a::comm_ring_1) poly) >0"
  obtains q where "p = q + (pochhammer_lt p)" and "degree q < degree p"
proof-
  let ?q = "p - (pochhammer_lt p)"
  let ?n = "degree p"
  have 0:"degree ?q < ?n" 
    using minus_pochhammer_leading_term assms by blast  
  then show ?thesis 
    using that by force 
qed

lemma pochhammer_monom_id:
  shows "(X - (of_nat n) + 1)*((PM a n) \<circ>\<^sub>p (X + 1)) = (X+1)*(PM a n)"
proof(induction n)
  case 0 
  then show ?case by (simp add: monom_0) 
next
  case (Suc n)
  fix n
  assume IH: "(X - (of_nat n) + 1)*((PM a n) \<circ>\<^sub>p (X + 1)) = (X+1)*(PM a n)"
  show "(X - (of_nat (Suc n)) + 1)*((PM a (Suc n)) \<circ>\<^sub>p (X + 1)) = (X+1)*(PM a (Suc n))"
    using pochhammer_monom_alt_def by (smt IH add.commute add_diff_cancel_left
        diff_add_eq mult.assoc mult.commute mult_smult_right
        of_nat_Suc pochhammer_monom_pcompose pochhammer_rec)
qed



(*******************Difference operator diff: p(x) \<Longrightarrow> p(x+1) - p(x)*******************************)

definition diff:: "('a::comm_ring_1) poly \<Rightarrow> ('a::comm_ring_1) poly" where
"diff p = pcompose  p [:1, 1:] - p"

(*difference operator is linear*)

lemma diff_additive:
"diff (p + q) = diff p + diff q"
  by (simp add: pcompose_add diff_def) 

lemma diff_smult:
"diff (smult a q) = smult a (diff q)"
  by (simp add: diff_def pcompose_smult smult_diff_right) 

lemma diff_mult_deg0:
  assumes "degree q = 0"
  shows "diff (q*p) = q* (diff p)"
  by (metis (no_types, lifting) assms degree_eq_zeroE 
      diff_def left_diff_distrib' mult.commute pcompose_const pcompose_mult) 

(**************************the difference operator evaluates as it should**************************)

lemma(in comm_ring_1)  diff_poly:
  shows "(poly (diff p)) x = ((poly p) (x+1)) - ((poly p) x)"
    by (simp add: diff_def poly_pcompose Groups.add_ac(2)) 

(******************************iterates of the difference operator*********************************)

fun diff_pow:: "nat \<Rightarrow> ('a::comm_ring_1) poly \<Rightarrow> 'a poly" ("\<Delta>[_]_ ") where
diff_pow_0: "diff_pow 0 p = p"|
diff_pow_suc: "diff_pow (Suc n) p = diff (diff_pow n p)"


lemma diff_pow_compose: "diff_pow (n+m) p = diff_pow n (diff_pow m p)"
proof(induction n arbitrary: m)
  case 0
  then show ?case
    by simp 
next  
  case (Suc n)
  then show ?case
    by simp 
qed

lemma diff_pow_additive: "diff_pow n (p+q) = (diff_pow n p) + (diff_pow n q)"
 proof(induction n)
  case 0
  then show ?case
    using diff_pow_0 by simp
next
  case (Suc n)
  then show ?case
    by (simp add: diff_additive) 
qed


(********************characterization of degree in terms of the difference operator****************)

lemma diff_const:
assumes "degree p = 0"
shows "diff p = 0"
proof-
  have "pcompose  p [:1, 1:] = p" 
    using assms by (metis degree_eq_zeroE pcompose_const) 
  then show ?thesis by (simp add: diff_def) 
qed

lemma diff_pow_const:
assumes "degree p = 0"
shows "diff_pow (Suc n) p = 0"
proof(induction n)
  case 0
  then show ?case 
    by (simp add: diff_const assms) 
next
  case (Suc n)
  then show ?case
    by (simp add: diff_const) 
qed

lemma one_not_zero:
"([:1:]:: ('a::comm_ring_1) poly) \<noteq> [:0:]" 
  by simp 

lemma diff_degree:
  assumes "degree (p::('a::{comm_ring_1}) poly) > 0"
  shows "degree p > (degree (diff p))"
proof- 
  have 0:"lead_coeff [:1, 1:] = 1"
    by simp   
  have "degree [:(1::'a), 1:] =  (Suc (degree [:1:]))" using  degree_pCons_eq one_not_zero 
    by simp 
  then have 1: "degree [:(1::'a), 1:] = 1"
    by simp 
  then have "degree ([:(1::'a), 1:]) > 0" 
    by simp  
  then have 2: "leading_term (pcompose  p [:1, 1:]) = leading_term p"
    by (metis (no_types, lifting) add.left_neutral
        add.right_neutral add_pCons degree_1  
          leading_term_monic_lin_comp one_pCons) 
  from 1 have "degree (pcompose p [:1,1:]) = degree p"
     by (metis "2" leading_term_degree) 
  then show ?thesis 
    using 2 assms(1) diff_def leading_term_eq_deg_less by metis
qed

(*remove SMT!*)
lemma diff_pow_degree0:
  assumes "degree (p::('a::{comm_ring_1}) poly) > 0"
  shows "n <degree p \<Longrightarrow>(degree p) - n \<ge> degree ((diff_pow n) p)"
proof(induction n)
  case 0
  then show ?case 
   by (simp add: assms(1)) 
next
  case (Suc n)
  fix n
  assume IH: "n < degree p \<Longrightarrow> degree (diff_pow n p) \<le> degree p - n"
  show "Suc n < degree p \<Longrightarrow> degree (diff_pow (Suc n) p) \<le> degree p - (Suc n)"
  proof-
    assume "Suc n < degree p"
    consider "degree (diff_pow n p) = 0" | "degree (diff_pow n p) >0"
      by blast
    have "degree (diff_pow n p) = 0 \<or> degree (diff_pow (Suc n) p) < degree (diff_pow n p)"
        using diff_pow_suc diff_degree  by auto
    then show ?thesis
      using IH by (smt Suc_diff_Suc \<open>Suc n < degree p\<close> 
          degree_0 diff_const le_Suc_eq less_Suc_eq_le 
          less_eq_nat.simps(1) less_le_trans not_le 
          pochhammer_monomials.diff_pow_suc)
  qed
qed


(********The nth iterate of the difference operator sends degree m<n polynomials to 0*************)

lemma diff_pow_zero:
  shows "degree (p::('a::{comm_ring_1}) poly) <n \<Longrightarrow> diff_pow n p = 0"
proof(cases "degree p = 0")
  case True
  assume  "degree p <n"
  then have "n >0" by auto
  then show "diff_pow n p = 0" using diff_pow_const 
    by (metis Suc_pred True) 
next
  case False
  assume A: "degree p <n"
  then have B: "degree p > 0" using False by simp
  let ?n = "(degree p) - 1"
  have "?n < degree p" using B by auto
  then have "1 \<ge> degree (diff_pow ?n  p)" using B diff_pow_degree0 
    by (metis One_nat_def Suc_diff_Suc 
        cancel_comm_monoid_add_class.diff_cancel
        diff_zero) 
  then have "degree (diff_pow (?n + 1) p) < 1" 
    by (metis One_nat_def add.commute
        degree_0 diff_const diff_degree diff_pow.simps(2) 
        le_Suc_eq le_zero_eq less_one plus_1_eq_Suc) 
  then have "degree (diff_pow (?n + 1) p) = 0" by auto
  then have "degree (diff_pow (?n + 1 + (n - (?n + 2))) p) = 0"
    using diff_pow_compose diff_pow_const  by (metis (no_types, lifting) Suc_diff_Suc
                                          add.commute add_cancel_left_right
                                          degree_0 neq0_conv zero_less_diff)  
  then have "degree (diff_pow (n-1) p) = 0"
    by (simp add: A B Suc_leI) 
  then show ?thesis 
    by (metis A B diff_Suc_1
        diff_const diff_pow.elims
        dual_order.strict_trans less_irrefl) 
qed




(************************Power rule for diff and pochhammer monomials****************************)

lemma diff_pochhammer_monom:
  "diff (PM a (Suc n)) = (of_nat (Suc n))*(PM a n)"
proof(induction n)
  case 0
  have P0: "(pochhammer_monom a (Suc 0)) = (monom a 1)"
    by (simp add: monom_altdef) 
  then have P1: "diff (pochhammer_monom a (Suc 0)) = pcompose  (monom a 1) [:1, 1:] - (monom a 1)" 
    by (simp add: diff_def) 
  then have "diff (pochhammer_monom a (Suc 0)) = monom a 0" 
    by (simp add: monom_0 monom_Suc pcompose_pCons) 
  then show ?case by simp 
next
  case (Suc n)
  fix n
  let ?n = "Suc n"
  assume IH: "diff (PM a ?n) = of_nat (?n) * (PM a n) "
  then show  "diff (PM a (Suc ?n)) = of_nat (Suc ?n) * PM a ?n"
  proof-
    have "(PM a (Suc ?n)) = (X - of_nat ?n)*(PM a ?n)"
      by simp 
    then have P: "diff (PM a (Suc ?n)) = (X  - of_nat ?n)\<circ>\<^sub>p (X + 1) *((PM a ?n) \<circ>\<^sub>p (X + 1)) - (X - of_nat ?n)*(PM a ?n)"
      by (simp add: diff_def one_pCons pcompose_mult)
    have Q:"(X  - of_nat ?n)\<circ>\<^sub>p (X + 1) =  (X   - (of_nat ?n) + 1)" 
      by (simp add: of_nat_poly one_pCons pcompose_pCons) 
    then have "diff (PM a (Suc ?n)) = (X + 1  - (of_nat ?n)) *((PM a ?n) \<circ>\<^sub>p (X + 1)) - (X - of_nat ?n)*(PM a ?n)"
      using  P by (smt diff_add_eq) 
    then have "diff (PM a (Suc ?n)) = (X+1)*(PM a ?n) - (X - of_nat ?n)*(PM a ?n)"
      by (metis P Q pochhammer_monom_id)
    then have "diff (PM a (Suc ?n)) = (1 +  of_nat ?n)*(PM a ?n)"
      by (metis (no_types, lifting)
          add_diff_cancel_left'
          diff_add_cancel diff_add_eq 
          left_diff_distrib')
    then show ?thesis by simp 
  qed
qed

(***********************************Generalized power rule*****************************************)

lemma diff_pow_pochhammer_monom0:
 shows "n \<ge> k \<Longrightarrow> (\<Delta>[k] (PM a (n+1))) = (pochhammer (of_nat (n + 2 - k)) k)*(PM a (n + 1 - k))"
proof(induction k)
  case 0
  then show ?case by simp 
next
  case (Suc k)
  show "\<And>k. (n \<ge> k \<Longrightarrow> (\<Delta>[k] (PM a (n + 1)))  = (pochhammer (of_nat  (n + 2 - k)) k) *( PM a  (n + 1 - k))) \<Longrightarrow>
            n \<ge>(Suc k) \<Longrightarrow> (\<Delta>[Suc k](PM a (n + 1)))  = (pochhammer (of_nat  (n + 2 - (Suc k))) (Suc k)) * (PM a (n + 1 - (Suc k)))"
  proof-
    fix k::nat
    show "(n \<ge>k \<Longrightarrow> (\<Delta>[k] (PM a (n + 1))) = (pochhammer (of_nat  (n + 2 - k)) k) *( PM a  (n + 1 - k))) \<Longrightarrow>
           n \<ge>(Suc k) \<Longrightarrow>   (\<Delta>[Suc k](PM a (n + 1)))  = (pochhammer (of_nat  (n + 2 - (Suc k))) (Suc k)) * (PM a (n + 1 - (Suc k)))"
    proof-
      assume IH0: "(n \<ge>k \<Longrightarrow> (\<Delta>[k] (PM a (n + 1)))  = (pochhammer (of_nat  (n + 2 - k)) k) *( PM a  (n + 1 - k)))"
      show "n \<ge>(Suc k) \<Longrightarrow> (\<Delta>[Suc k](PM a (n + 1))) = (pochhammer (of_nat  (n + 2 - (Suc k))) (Suc k)) * (PM a (n + 1 - (Suc k)))"
      proof-
        assume A: "n \<ge>(Suc k)"
        show " (\<Delta>[Suc k](PM a (n + 1)))  =  (pochhammer (of_nat  (n + 2 - (Suc k))) (Suc k)) * (PM a (n + 1 - (Suc k)))"
        proof-
          have IH: "(\<Delta>[k] (PM a (n + 1))) = (pochhammer (of_nat  (n + 2 - k)) k) *( PM a  (n + 1 - k))" 
            using IH0 Suc_lessD A Suc_leD by blast  
          let ?p = "(\<Delta>[k] (PM a (n+1)))"
          let ?q = " (pochhammer (of_nat  (n + 2 - k)) k) *( PM a  (n + 1 - k))"  
          have  "?p = ?q" using IH by blast  
          then have I: "diff ?p = diff ?q" by simp
          have  "(\<Delta>[Suc k] (PM a (n+1))) = diff ?p"  by simp
          then have P: "(\<Delta>[Suc k] (PM a (n+1))) = diff ?q" using I by auto 
          have Q: "diff ?q = (pochhammer (of_nat (n + 2 - k)) k)*(diff (PM a (n + 1 - k)))" 
            using diff_mult_deg0 by (metis degree_of_nat pochhammer_of_nat) 
          then have R: "diff ?q = (pochhammer (of_nat (n + 2 - k)) k)
                            *(of_nat (n + 1 - k))*(PM a (n - k))"
            using diff_pochhammer_monom  by (metis (no_types, lifting)
                    A Suc_diff_le Suc_leD add.commute mult.assoc plus_1_eq_Suc) 
          have  "(pochhammer (of_nat (n + 2 - k)) k)*(of_nat (n + 1 - k))
               =  (pochhammer (of_nat (n +  1 - k)) (Suc k))"
            by (simp add: A Suc_diff_le Suc_leD
                add.commute mult.commute pochhammer_rec) 
          then have S: "diff ?q = (pochhammer (of_nat (n + 1 - k)) (Suc k))*(PM a (n - k))"
            using R  by metis  
          then have T: "(\<Delta>[Suc k] (PM a (n+1)))
               = (pochhammer (of_nat (n + 1 - k)) (Suc k))*(PM a (n - k))"
            using P by simp
          have "n + 2 - (Suc k) =  n + 1 - k"
            using A by linarith 
          then have "(\<Delta>[Suc k] (PM a (n+1)))
                 = (pochhammer (of_nat (n + 2 - (Suc k) )) (Suc k))*(PM a (n + 1 - (Suc k)))"
            using T by auto
          then show ?thesis by auto
        qed
      qed
    qed
  qed
qed

lemma diff_pow_pochhammer_monom1: 
"(\<Delta>[n] (PM a (n))) = (pochhammer (of_nat (1)) n)* (PM a (0))"
proof(cases "n = 0")
  case True
  then show ?thesis by simp 
next 
  case False
  let ?n = "n-1"
  have P: "(\<Delta>[?n] (PM a (?n+1))) = (pochhammer (of_nat (2)) ?n)*(PM a 1)"
     using diff_pow_pochhammer_monom0 by (metis (no_types, lifting) add.right_neutral
                                     add_diff_cancel_left' le_numeral_extra(3)
                                      nat_add_left_cancel_le of_nat_1 of_nat_add one_add_one)  
  then have "(\<Delta>[n] (PM a (n))) = diff (\<Delta>[?n] (PM a (?n+1)))"
     using False by (metis One_nat_def Suc_diff_Suc
         add.commute diff_zero neq0_conv
         plus_1_eq_Suc pochhammer_monomials.diff_pow_suc) 
  then have "(\<Delta>[n] (PM a (n))) = diff ((pochhammer (of_nat (2)) ?n)*(PM a 1))" using P
     by auto
  then have Q:  "(\<Delta>[n] (PM a (n))) = (pochhammer (of_nat 2) ?n)*(diff (PM a 1))" 
     using diff_mult_deg0 by (metis degree_of_nat pochhammer_of_nat) 
  have "(diff (PM a 1)) =((of_nat 1)*((PM a 0)))" 
    using diff_pochhammer_monom  by (metis One_nat_def) 
  then have  "(\<Delta>[n] (PM a (n))) = (pochhammer (of_nat 2) ?n)*((of_nat 1)*(PM a 0))" 
    using Q by simp
  then show ?thesis  by (simp add: pochhammer_rec_if) 
qed

lemma diff_pow_pochhammer_monom:
 assumes "a \<noteq>0"
 shows "(\<Delta>[k] (PM (a::('a::comm_ring_1)) (n+1))) 
                = (pochhammer (of_nat (n + 2 - k)) k)*(PM a (n + 1 - k))"
proof(cases "n + 1 \<ge>k")
  case True
  then show ?thesis 
  proof(cases "n \<ge>k")
    case True 
    then show ?thesis 
      using diff_pow_pochhammer_monom0 by blast 
  next
    case F: False 
    then show ?thesis 
      using True F diff_pow_pochhammer_monom1  by (metis One_nat_def Suc_diff_le
          add.commute add_2_eq_Suc' diff_diff_cancel 
          diff_is_0_eq diff_zero not_less_eq_eq plus_1_eq_Suc)  
  qed
  next
   case F: False
   have IE: "k > n+1" using F by auto
   let ?p = "PM (a::('a::comm_ring_1)) (n+1)" 
   have "degree ?p = n+1" 
     using assms pochhammer_monom_degree by blast 
   then have "degree ?p < k"
     using IE by auto 
   then have A: "(\<Delta>[k] ?p) = 0" using diff_pow_zero 
     by blast 
   have "(pochhammer (of_nat (n + 2 - k)) k) = 0"
      by (metis F Suc_eq_plus1 add_2_eq_Suc'
       diff_is_0_eq' eq_imp_le le_trans linorder_not_le
       not_less_eq_eq of_nat_0 pochhammer_0_left  zero_less_Suc)
   then have  "(pochhammer (of_nat (n + 2 - k)) k)*(PM a (n + 1 - k)) = 0"
     using mult_not_zero by blast 
   then have " ((pochhammer (of_nat (n + 2 - k)) k)*(PM a (n + 1 - k))) = 0"
     by blast 
   then show "(\<Delta>[k] (PM (a::('a::comm_ring_1)) (n+1))) = (pochhammer (of_nat (n + 2 - k)) k)*(PM a (n + 1 - k))"
     using A by auto
qed

lemma diff_pow_greater_deg:
  assumes "a \<noteq>0"
  assumes "k>n"
  shows "(\<Delta>[k](PM (a::('a::comm_ring_1)) n)) = 0"
proof-  
  let ?n = "k - n"
  have "(\<Delta>[k](PM (a::('a::comm_ring_1)) n)) = \<Delta>[?n](\<Delta>[n](PM (a::('a::comm_ring_1)) n))"
    by (metis add.commute assms(2)
        diff_pow_compose le_add_diff_inverse
        linorder_not_le nat_le_linear) 
  then have "(\<Delta>[k](PM (a::('a::comm_ring_1)) n)) = \<Delta>[?n]((pochhammer 2 n))"
    by (metis assms(1) assms(2) degree_of_nat
        diff_pow_zero of_nat_numeral 
        pochhammer_monom_degree pochhammer_of_nat
        zero_less_diff) 
  then show "(\<Delta>[k](PM (a::('a::comm_ring_1)) n)) = 0" 
    by (simp add: assms(1) assms(2) diff_pow_zero pochhammer_monom_degree) 
qed

end