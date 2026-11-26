/-
Coordinator-integrated from the independently rebuilt `smwxb4a1l/m1` Q5 artifact.
Original production base `8d1c9eb3738a26cc63afc07f525ba4af357bd905`; review revisions
are confined to strict module lints and explicit branch-lemma aggregation.
-/
/-
Independently built for swarm `smwxb4a1l`, member `m1`, direction Q5-FINITE-EVALUATION.
Read-only against production (`d9a001b7f0a33cf6395158f7621ad4de1fe3c7c8`).
Proofs only in this file; no new definitions.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Five.CoverFive
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Five.Engine

/-!
# The summed `q = 5` fresh-copy factor of Lemma I.4.17

The `q = 5` cover (`freshMark_subset_q5Shape`) and its BK bound (`freshMark_measure_le_q5`) give,
for every arm tuple `g`, selected arm `j` and ordering `i1, i2, i3, i4` of the other four labels,

  `P(freshMark y g j w) ≤ ∑_{k1,k2,k3,k4} ∑_{z1,z2,z3,z4} ∏_{10 legs} τ(leg)`,

a sum of `2 · 4 · 6 · 8 = 384` members of ten two-point factors each.  This file evaluates it:

* `Equiv.tsum_eq` along `armEquiv5` reindexes `∑' g : Fin 5 → V` to `∑' pa : V × V × V × V × V`,
  so the five arm labels are retained, not collapsed;
* `arms_inner_five` moves the arm tuple inside, where `tsum_arm_five_tuple` sums the five arms to
  `χ⁵` (already done inside each `ev_<n>`);
* `tsum_fin2`, `tsum_fin2_bool`, `tsum_fin2_bool_bool`, `tsum_idx3` expand the four finite branch
  sums;
* the `384` fully instantiated branch evaluations `ev_0 … ev_383` produce `χ^(10-ℓ) T^ℓ`;
* the evaluated members recombine into `freshFiveProfile`
  `24 χ⁵ T⁵ + 60 χ⁶ T⁴ + 90 χ⁷ T³ + 105 χ⁸ T² + 105 χ⁹ T`.

The `T`-power range is `[1, 5]` and every monomial carries `(10 - ℓ) + ℓ = 10 = 2q` two-point
factors; after composition with the `2p + 1`-edge marked side the factor count is `2p + 11` and the
path powers lie in the printed interval.  Only the constant row sum and BK are used.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSimpArgs false
@[expose] public section

namespace PercLib.CriticalLRP.I417FreshFive

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417FreshFour.Refined
open PercLib.CriticalLRP.I417FreshFour.Eval
open PercLib.CriticalLRP.I417GenIter
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417Base

variable {V : Type*} [Countable V] [DecidableEq V]

set_option maxHeartbeats 4000000 in
-- The aggregation elaborates 384 branch-evaluation rewrites in one declaration.
/-- **The `q = 5` fresh-copy factor, summed over the five-arm tuple and evaluated.** -/
theorem tsum_q5_le_profile (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (χ : ℝ≥0∞) (hχ : ∀ v : V, ∑' z : V, tau π v z = χ)
    (j i1 i2 i3 i4 : Fin 5) (h01 : j ≠ i1) (h02 : j ≠ i2) (h03 : j ≠ i3) (h04 : j ≠ i4)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h14 : i1 ≠ i4) (h23 : i2 ≠ i3) (h24 : i2 ≠ i4)
    (h34 : i3 ≠ i4) :
    (∑' g : Fin 5 → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      freshFiveProfile π χ y w := by
  classical
  refine le_trans (ENNReal.tsum_le_tsum fun g =>
    freshMark_measure_le_q5 π hπ y w g j i1 i2 i3 i4) ?_
  have hre : (∑' g : Fin 5 → V,
        ∑' (k1 : Fin 2), ∑' (k2 : Fin 2 ⊕ Bool), ∑' (k3 : (Fin 2 ⊕ Bool) ⊕ Bool),
          ∑' (k4 : ((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool), ∑' (z1 : V), ∑' (z2 : V), ∑' (z3 : V),
          ∑' (z4 : V),
            ∏ i, tau π
              (q5Legs k1 k2 k3 k4 z1 z2 z3 z4 y w (g j) (g i1) (g i2) (g i3) (g i4) i).1
              (q5Legs k1 k2 k3 k4 z1 z2 z3 z4 y w (g j) (g i1) (g i2) (g i3) (g i4) i).2) =
      (∑' pa : V × V × V × V × V,
        ∑' (k1 : Fin 2), ∑' (k2 : Fin 2 ⊕ Bool), ∑' (k3 : (Fin 2 ⊕ Bool) ⊕ Bool),
          ∑' (k4 : ((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool), ∑' (z1 : V), ∑' (z2 : V), ∑' (z3 : V),
          ∑' (z4 : V),
            ∏ i, tau π
              (q5Legs k1 k2 k3 k4 z1 z2 z3 z4 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2.1 pa.2.2.2.2
                i).1
              (q5Legs k1 k2 k3 k4 z1 z2 z3 z4 y w pa.1 pa.2.1 pa.2.2.1 pa.2.2.2.1 pa.2.2.2.2
                i).2) :=
    Equiv.tsum_eq (armEquiv5 j i1 i2 i3 i4 h01 h02 h03 h04 h12 h13 h14 h23 h24 h34)
      (fun p : V × V × V × V × V =>
        ∑' (k1 : Fin 2), ∑' (k2 : Fin 2 ⊕ Bool), ∑' (k3 : (Fin 2 ⊕ Bool) ⊕ Bool),
          ∑' (k4 : ((Fin 2 ⊕ Bool) ⊕ Bool) ⊕ Bool), ∑' (z1 : V), ∑' (z2 : V), ∑' (z3 : V),
          ∑' (z4 : V),
            ∏ i, tau π
              (q5Legs k1 k2 k3 k4 z1 z2 z3 z4 y w p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 i).1
              (q5Legs k1 k2 k3 k4 z1 z2 z3 z4 y w p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 i).2)
  refine le_trans (le_of_eq hre) ?_
  rw [arms_inner_five]
  conv_lhs => simp only [tsum_fin2, tsum_fin2_bool, tsum_fin2_bool_bool, tsum_idx3]
  rw [ev_0 π y w χ hχ, ev_1 π y w χ hχ, ev_2 π y w χ hχ, ev_3 π y w χ hχ, ev_4 π y w χ hχ, ev_5 π y w χ hχ, ev_6 π y w χ hχ, ev_7 π y w χ hχ,
  ev_8 π y w χ hχ, ev_9 π y w χ hχ, ev_10 π y w χ hχ, ev_11 π y w χ hχ, ev_12 π y w χ hχ, ev_13 π y w χ hχ, ev_14 π y w χ hχ, ev_15 π y w χ hχ,
  ev_16 π y w χ hχ, ev_17 π y w χ hχ, ev_18 π y w χ hχ, ev_19 π y w χ hχ, ev_20 π y w χ hχ, ev_21 π y w χ hχ, ev_22 π y w χ hχ, ev_23 π y w χ hχ,
  ev_24 π y w χ hχ, ev_25 π y w χ hχ, ev_26 π y w χ hχ, ev_27 π y w χ hχ, ev_28 π y w χ hχ, ev_29 π y w χ hχ, ev_30 π y w χ hχ, ev_31 π y w χ hχ,
  ev_32 π y w χ hχ, ev_33 π y w χ hχ, ev_34 π y w χ hχ, ev_35 π y w χ hχ, ev_36 π y w χ hχ, ev_37 π y w χ hχ, ev_38 π y w χ hχ, ev_39 π y w χ hχ,
  ev_40 π y w χ hχ, ev_41 π y w χ hχ, ev_42 π y w χ hχ, ev_43 π y w χ hχ, ev_44 π y w χ hχ, ev_45 π y w χ hχ, ev_46 π y w χ hχ, ev_47 π y w χ hχ,
  ev_48 π y w χ hχ, ev_49 π y w χ hχ, ev_50 π y w χ hχ, ev_51 π y w χ hχ, ev_52 π y w χ hχ, ev_53 π y w χ hχ, ev_54 π y w χ hχ, ev_55 π y w χ hχ,
  ev_56 π y w χ hχ, ev_57 π y w χ hχ, ev_58 π y w χ hχ, ev_59 π y w χ hχ, ev_60 π y w χ hχ, ev_61 π y w χ hχ, ev_62 π y w χ hχ, ev_63 π y w χ hχ,
  ev_64 π y w χ hχ, ev_65 π y w χ hχ, ev_66 π y w χ hχ, ev_67 π y w χ hχ, ev_68 π y w χ hχ, ev_69 π y w χ hχ, ev_70 π y w χ hχ, ev_71 π y w χ hχ,
  ev_72 π y w χ hχ, ev_73 π y w χ hχ, ev_74 π y w χ hχ, ev_75 π y w χ hχ, ev_76 π y w χ hχ, ev_77 π y w χ hχ, ev_78 π y w χ hχ, ev_79 π y w χ hχ,
  ev_80 π y w χ hχ, ev_81 π y w χ hχ, ev_82 π y w χ hχ, ev_83 π y w χ hχ, ev_84 π y w χ hχ, ev_85 π y w χ hχ, ev_86 π y w χ hχ, ev_87 π y w χ hχ,
  ev_88 π y w χ hχ, ev_89 π y w χ hχ, ev_90 π y w χ hχ, ev_91 π y w χ hχ, ev_92 π y w χ hχ, ev_93 π y w χ hχ, ev_94 π y w χ hχ, ev_95 π y w χ hχ,
  ev_96 π y w χ hχ, ev_97 π y w χ hχ, ev_98 π y w χ hχ, ev_99 π y w χ hχ, ev_100 π y w χ hχ, ev_101 π y w χ hχ, ev_102 π y w χ hχ, ev_103 π y w χ hχ,
  ev_104 π y w χ hχ, ev_105 π y w χ hχ, ev_106 π y w χ hχ, ev_107 π y w χ hχ, ev_108 π y w χ hχ, ev_109 π y w χ hχ, ev_110 π y w χ hχ, ev_111 π y w χ hχ,
  ev_112 π y w χ hχ, ev_113 π y w χ hχ, ev_114 π y w χ hχ, ev_115 π y w χ hχ, ev_116 π y w χ hχ, ev_117 π y w χ hχ, ev_118 π y w χ hχ, ev_119 π y w χ hχ,
  ev_120 π y w χ hχ, ev_121 π y w χ hχ, ev_122 π y w χ hχ, ev_123 π y w χ hχ, ev_124 π y w χ hχ, ev_125 π y w χ hχ, ev_126 π y w χ hχ, ev_127 π y w χ hχ,
  ev_128 π y w χ hχ, ev_129 π y w χ hχ, ev_130 π y w χ hχ, ev_131 π y w χ hχ, ev_132 π y w χ hχ, ev_133 π y w χ hχ, ev_134 π y w χ hχ, ev_135 π y w χ hχ,
  ev_136 π y w χ hχ, ev_137 π y w χ hχ, ev_138 π y w χ hχ, ev_139 π y w χ hχ, ev_140 π y w χ hχ, ev_141 π y w χ hχ, ev_142 π y w χ hχ, ev_143 π y w χ hχ,
  ev_144 π y w χ hχ, ev_145 π y w χ hχ, ev_146 π y w χ hχ, ev_147 π y w χ hχ, ev_148 π y w χ hχ, ev_149 π y w χ hχ, ev_150 π y w χ hχ, ev_151 π y w χ hχ,
  ev_152 π y w χ hχ, ev_153 π y w χ hχ, ev_154 π y w χ hχ, ev_155 π y w χ hχ, ev_156 π y w χ hχ, ev_157 π y w χ hχ, ev_158 π y w χ hχ, ev_159 π y w χ hχ,
  ev_160 π y w χ hχ, ev_161 π y w χ hχ, ev_162 π y w χ hχ, ev_163 π y w χ hχ, ev_164 π y w χ hχ, ev_165 π y w χ hχ, ev_166 π y w χ hχ, ev_167 π y w χ hχ,
  ev_168 π y w χ hχ, ev_169 π y w χ hχ, ev_170 π y w χ hχ, ev_171 π y w χ hχ, ev_172 π y w χ hχ, ev_173 π y w χ hχ, ev_174 π y w χ hχ, ev_175 π y w χ hχ,
  ev_176 π y w χ hχ, ev_177 π y w χ hχ, ev_178 π y w χ hχ, ev_179 π y w χ hχ, ev_180 π y w χ hχ, ev_181 π y w χ hχ, ev_182 π y w χ hχ, ev_183 π y w χ hχ,
  ev_184 π y w χ hχ, ev_185 π y w χ hχ, ev_186 π y w χ hχ, ev_187 π y w χ hχ, ev_188 π y w χ hχ, ev_189 π y w χ hχ, ev_190 π y w χ hχ, ev_191 π y w χ hχ,
  ev_192 π y w χ hχ, ev_193 π y w χ hχ, ev_194 π y w χ hχ, ev_195 π y w χ hχ, ev_196 π y w χ hχ, ev_197 π y w χ hχ, ev_198 π y w χ hχ, ev_199 π y w χ hχ,
  ev_200 π y w χ hχ, ev_201 π y w χ hχ, ev_202 π y w χ hχ, ev_203 π y w χ hχ, ev_204 π y w χ hχ, ev_205 π y w χ hχ, ev_206 π y w χ hχ, ev_207 π y w χ hχ,
  ev_208 π y w χ hχ, ev_209 π y w χ hχ, ev_210 π y w χ hχ, ev_211 π y w χ hχ, ev_212 π y w χ hχ, ev_213 π y w χ hχ, ev_214 π y w χ hχ, ev_215 π y w χ hχ,
  ev_216 π y w χ hχ, ev_217 π y w χ hχ, ev_218 π y w χ hχ, ev_219 π y w χ hχ, ev_220 π y w χ hχ, ev_221 π y w χ hχ, ev_222 π y w χ hχ, ev_223 π y w χ hχ,
  ev_224 π y w χ hχ, ev_225 π y w χ hχ, ev_226 π y w χ hχ, ev_227 π y w χ hχ, ev_228 π y w χ hχ, ev_229 π y w χ hχ, ev_230 π y w χ hχ, ev_231 π y w χ hχ,
  ev_232 π y w χ hχ, ev_233 π y w χ hχ, ev_234 π y w χ hχ, ev_235 π y w χ hχ, ev_236 π y w χ hχ, ev_237 π y w χ hχ, ev_238 π y w χ hχ, ev_239 π y w χ hχ,
  ev_240 π y w χ hχ, ev_241 π y w χ hχ, ev_242 π y w χ hχ, ev_243 π y w χ hχ, ev_244 π y w χ hχ, ev_245 π y w χ hχ, ev_246 π y w χ hχ, ev_247 π y w χ hχ,
  ev_248 π y w χ hχ, ev_249 π y w χ hχ, ev_250 π y w χ hχ, ev_251 π y w χ hχ, ev_252 π y w χ hχ, ev_253 π y w χ hχ, ev_254 π y w χ hχ, ev_255 π y w χ hχ,
  ev_256 π y w χ hχ, ev_257 π y w χ hχ, ev_258 π y w χ hχ, ev_259 π y w χ hχ, ev_260 π y w χ hχ, ev_261 π y w χ hχ, ev_262 π y w χ hχ, ev_263 π y w χ hχ,
  ev_264 π y w χ hχ, ev_265 π y w χ hχ, ev_266 π y w χ hχ, ev_267 π y w χ hχ, ev_268 π y w χ hχ, ev_269 π y w χ hχ, ev_270 π y w χ hχ, ev_271 π y w χ hχ,
  ev_272 π y w χ hχ, ev_273 π y w χ hχ, ev_274 π y w χ hχ, ev_275 π y w χ hχ, ev_276 π y w χ hχ, ev_277 π y w χ hχ, ev_278 π y w χ hχ, ev_279 π y w χ hχ,
  ev_280 π y w χ hχ, ev_281 π y w χ hχ, ev_282 π y w χ hχ, ev_283 π y w χ hχ, ev_284 π y w χ hχ, ev_285 π y w χ hχ, ev_286 π y w χ hχ, ev_287 π y w χ hχ,
  ev_288 π y w χ hχ, ev_289 π y w χ hχ, ev_290 π y w χ hχ, ev_291 π y w χ hχ, ev_292 π y w χ hχ, ev_293 π y w χ hχ, ev_294 π y w χ hχ, ev_295 π y w χ hχ,
  ev_296 π y w χ hχ, ev_297 π y w χ hχ, ev_298 π y w χ hχ, ev_299 π y w χ hχ, ev_300 π y w χ hχ, ev_301 π y w χ hχ, ev_302 π y w χ hχ, ev_303 π y w χ hχ,
  ev_304 π y w χ hχ, ev_305 π y w χ hχ, ev_306 π y w χ hχ, ev_307 π y w χ hχ, ev_308 π y w χ hχ, ev_309 π y w χ hχ, ev_310 π y w χ hχ, ev_311 π y w χ hχ,
  ev_312 π y w χ hχ, ev_313 π y w χ hχ, ev_314 π y w χ hχ, ev_315 π y w χ hχ, ev_316 π y w χ hχ, ev_317 π y w χ hχ, ev_318 π y w χ hχ, ev_319 π y w χ hχ,
  ev_320 π y w χ hχ, ev_321 π y w χ hχ, ev_322 π y w χ hχ, ev_323 π y w χ hχ, ev_324 π y w χ hχ, ev_325 π y w χ hχ, ev_326 π y w χ hχ, ev_327 π y w χ hχ,
  ev_328 π y w χ hχ, ev_329 π y w χ hχ, ev_330 π y w χ hχ, ev_331 π y w χ hχ, ev_332 π y w χ hχ, ev_333 π y w χ hχ, ev_334 π y w χ hχ, ev_335 π y w χ hχ,
  ev_336 π y w χ hχ, ev_337 π y w χ hχ, ev_338 π y w χ hχ, ev_339 π y w χ hχ, ev_340 π y w χ hχ, ev_341 π y w χ hχ, ev_342 π y w χ hχ, ev_343 π y w χ hχ,
  ev_344 π y w χ hχ, ev_345 π y w χ hχ, ev_346 π y w χ hχ, ev_347 π y w χ hχ, ev_348 π y w χ hχ, ev_349 π y w χ hχ, ev_350 π y w χ hχ, ev_351 π y w χ hχ,
  ev_352 π y w χ hχ, ev_353 π y w χ hχ, ev_354 π y w χ hχ, ev_355 π y w χ hχ, ev_356 π y w χ hχ, ev_357 π y w χ hχ, ev_358 π y w χ hχ, ev_359 π y w χ hχ,
  ev_360 π y w χ hχ, ev_361 π y w χ hχ, ev_362 π y w χ hχ, ev_363 π y w χ hχ, ev_364 π y w χ hχ, ev_365 π y w χ hχ, ev_366 π y w χ hχ, ev_367 π y w χ hχ,
  ev_368 π y w χ hχ, ev_369 π y w χ hχ, ev_370 π y w χ hχ, ev_371 π y w χ hχ, ev_372 π y w χ hχ, ev_373 π y w χ hχ, ev_374 π y w χ hχ, ev_375 π y w χ hχ,
  ev_376 π y w χ hχ, ev_377 π y w χ hχ, ev_378 π y w χ hχ, ev_379 π y w χ hχ, ev_380 π y w χ hχ, ev_381 π y w χ hχ, ev_382 π y w χ hχ, ev_383 π y w χ hχ]
  rw [freshFiveProfile]
  have hk : (fun a b : V => (edgeMeasure π) (connSet a b)) = I417FreshTwo.kernel π := by
    funext a b
    exact (I417FreshTwo.kernel_def π a b).symm
  rw [hk]
  refine le_of_eq ?_
  ring

/-- **The `q = 5` fresh-copy factor for every selected arm `j : Fin 5`.** -/
theorem tsum_freshMark_le_profile_five (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (y w : V) (χ : ℝ≥0∞) (hχ : ∀ v : V, ∑' z : V, tau π v z = χ) (j : Fin 5) :
    (∑' g : Fin 5 → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      freshFiveProfile π χ y w := by
  fin_cases j
  · exact tsum_q5_le_profile π hπ y w χ hχ 0 1 2 3 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact tsum_q5_le_profile π hπ y w χ hχ 1 0 2 3 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact tsum_q5_le_profile π hπ y w χ hχ 2 0 1 3 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact tsum_q5_le_profile π hπ y w χ hχ 3 0 1 2 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact tsum_q5_le_profile π hπ y w χ hχ 4 0 1 2 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end PercLib.CriticalLRP.I417FreshFive

namespace PercLib.CriticalLRP.I417FreshFive

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417FreshFour.Refined
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417Base

variable {V : Type*} [Countable V] [DecidableEq V]

/-- **The `q = 5` fresh-evaluation premise, discharged.**  The `q = 5` analogue of
`I417FreshFour.Refined.FreshFourEval`: for every constant row sum `χ`, every `y, w` and every
selected arm `j : Fin 5`, the fresh marked event summed over the five-arm tuple is bounded by the
profile `24 χ⁵ T⁵ + 60 χ⁶ T⁴ + 90 χ⁷ T³ + 105 χ⁸ T² + 105 χ⁹ T`.  The only inputs are a constant row
sum and BK (`π e < 1`); no moment or finiteness hypothesis. -/
theorem freshFiveEval_holds (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) :
    ∀ (χ : ℝ≥0∞), (∀ v : V, ∑' z : V, tau π v z = χ) →
      ∀ (y w : V) (j : Fin 5),
        (∑' g : Fin 5 → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
          freshFiveProfile π χ y w := by
  intro χ hχ y w j
  exact tsum_freshMark_le_profile_five π hπ y w χ hχ j

end PercLib.CriticalLRP.I417FreshFive
