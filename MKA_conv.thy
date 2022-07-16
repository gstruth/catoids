(* 
Title: Modal Kleene Algebra with Converse
Author: Cameron Calk, Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Modal Kleene algebra with Converse\<close>

theory "MKA_conv"
  imports MKA_light KA_conv

begin

text \<open>Here we mainly study the interaction of converse with domain and codomain.\<close>

subsection \<open>Involutive modal Kleene algebras\<close>

class involutive_domain_semiring = domain_semiring + involutive_dioid

begin

lemma "dom ((dom x)\<^sup>\<circ>) = dom x"
  nitpick (* 4-element counterexample *)
  oops

lemma "(dom x = x) = (x = dom (x\<^sup>\<circ>  ))"
  nitpick  (* 4-element counterexample *)
  oops

lemma strong_conv_conv: "dom x \<le> x \<cdot> x\<^sup>\<circ> \<Longrightarrow> x \<le> x \<cdot> x\<^sup>\<circ> \<cdot> x"
proof-
  assume h: "dom x \<le> x \<cdot> x\<^sup>\<circ>"
  have "x = dom x \<cdot> x"
    by simp
  also have "\<dots> \<le>  x \<cdot> x\<^sup>\<circ> \<cdot> x"
    using h local.mult_isor by presburger
  finally show ?thesis.
qed

end

class involutive_modal_semiring  = modal_semiring + involutive_dioid

begin

lemma "dom (x\<^sup>\<circ>) = cod x"
  nitpick (* 4-element counterexample *)
  oops

lemma "(dom x)\<^sup>\<circ> = dom x"
  nitpick (* 4-element counterexample *)
  oops

lemma "(cod x)\<^sup>\<circ> = cod x"
  nitpick (* 4-element counterexample *)
  oops

lemma "dom (x\<^sup>\<circ>) = cod x \<Longrightarrow> cod (x\<^sup>\<circ>) = dom x \<Longrightarrow> (dom x)\<^sup>\<circ> = dom x"
  nitpick (* 5-element counterexample *)
  oops

end

class involutive_modal_kleene_algebra = involutive_modal_semiring + kleene_algebra


subsection \<open>Modal Kleene algebras with converse\<close>

class modal_semiring_converse = modal_semiring + dioid_converse

begin

lemma d_conv [simp]: "(dom x)\<^sup>\<circ> = dom x"
proof-
  have "dom x \<le> dom x \<cdot> (dom x)\<^sup>\<circ> \<cdot> dom x"
    by (simp add: local.strong_gelfand)
  also have  "\<dots> \<le> 1 \<cdot> (dom x)\<^sup>\<circ> \<cdot> 1"
    using local.d_subid local.dd.mult_iso by blast
  finally have a: "dom x \<le> (dom x)\<^sup>\<circ>"
    by simp
  hence "(dom x)\<^sup>\<circ> \<le> dom x"
    by (simp add: local.inv_adj)
  thus ?thesis
    using a by auto
qed

lemma cod_conv: "(cod x)\<^sup>\<circ> = cod x"
  by (metis d_conv local.dc_compat)

lemma d_conv_cod [simp]: "dom (x\<^sup>\<circ>) = cod x"
proof-
  have "dom (x\<^sup>\<circ>) = dom ((x \<cdot> cod x)\<^sup>\<circ>)"
    by simp
  also have "\<dots> = dom ((cod x)\<^sup>\<circ> \<cdot> x\<^sup>\<circ>)"
    using local.inv_contrav by presburger
  also have "\<dots> = dom (cod x \<cdot> x\<^sup>\<circ>)"
    by (simp add: cod_conv)
  also have "\<dots> = dom (dom (cod x) \<cdot> x\<^sup>\<circ>)"
    by simp
  also have "\<dots> = dom (cod x) \<cdot> dom (x\<^sup>\<circ>)"
    using local.d_export by blast
  also have "\<dots> = cod x \<cdot> dom (x\<^sup>\<circ>)"
    by simp
  also have "\<dots> = cod x \<cdot> cod (dom (x\<^sup>\<circ>))"
    by simp
  also have "\<dots> = cod (x \<cdot> cod (dom (x\<^sup>\<circ>)))"
    using local.coddual.d_export by presburger
  also have "\<dots> = cod (x \<cdot> dom (x\<^sup>\<circ>))"
    by simp
  also have "\<dots> = cod ((x\<^sup>\<circ>)\<^sup>\<circ> \<cdot> (dom (x\<^sup>\<circ>))\<^sup>\<circ>)"
    by simp
  also have "\<dots> = cod ((dom (x\<^sup>\<circ>) \<cdot> x\<^sup>\<circ>)\<^sup>\<circ>)"
    using local.inv_contrav by presburger
  also have "\<dots> = cod ((x\<^sup>\<circ>)\<^sup>\<circ>)"
    by simp
  also have "\<dots> = cod x"
    by simp
  finally show ?thesis.
qed

lemma cod_conv_d: "cod (x\<^sup>\<circ>) = dom x"
  by (metis d_conv_cod local.inv_invol)

lemma "dom y = y \<Longrightarrow> fdia (x\<^sup>\<circ>) y = bdia x y"
proof-
  assume h: "dom y = y"
  have "fdia (x\<^sup>\<circ>) y = dom (x\<^sup>\<circ> \<cdot> dom y)"
    by (simp add: local.fdia_def)
  also have "\<dots> = dom ((dom y \<cdot> x)\<^sup>\<circ>)"
    by simp
  also have "\<dots> = cod (dom y \<cdot> x)"
    using d_conv_cod by blast
  also have "\<dots> = bdia x y"
    by (simp add: h local.coddual.fdia_def)
  finally show ?thesis.
qed

lemma "dom y = y \<Longrightarrow> bdia (x\<^sup>\<circ>) y = fdia x y"
  by (metis cod_conv_d d_conv local.coddual.fdia_def local.fdia_def local.inv_contrav)

lemma "dom x \<le> x \<cdot> x\<^sup>\<circ>"
  nitpick (* 3-element counterexample *)
  oops

end

class modal_kleene_algebra_converse = modal_semiring_converse + kleene_algebra

class modal_semiring_strong_converse = involutive_modal_semiring + 
  assumes weak_dom_def: "dom x \<le> x \<cdot> x\<^sup>\<circ>"
  and weak_cod_def: "cod x \<le> x\<^sup>\<circ> \<cdot> x"

subclass (in modal_semiring_strong_converse) modal_semiring_converse
  by (unfold_locales, metis local.coddual.d_absorb_eq local.dd.mult_assoc local.mult_isol local.weak_cod_def)

class modal_kleene_algebra_strong_converse = modal_semiring_strong_converse + kleene_algebra

end
