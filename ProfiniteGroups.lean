/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.EpiMono
public import ProfiniteGroups.ContinuousSection
public import ProfiniteGroups.FiniteQuotientHom
public import ProfiniteGroups.CompatibleSubgroups
public import ProfiniteGroups.CompatibleSylow
public import ProfiniteGroups.ClosedSylow
public import ProfiniteGroups.FiniteQuotientConjugacy
public import ProfiniteGroups.FreeProduct
public import ProfiniteGroups.FinitePresentation
public import ProfiniteGroups.ProP
public import ProfiniteGroups.Procyclic
public import ProfiniteGroups.PrimewisePadic
public import ProfiniteGroups.PrimewisePadicKernel
public import ProfiniteGroups.ClosedIdealPi
public import ProfiniteGroups.PrimewisePadicIdeals
public import ProfiniteGroups.PrimewisePadicIdealTransport
public import ProfiniteGroups.PrimewisePadicSubgroups
public import ProfiniteGroups.PiIdealQuotient
public import ProfiniteGroups.PrimewisePadicQuotients
public import ProfiniteGroups.ProcyclicQuotient
public import ProfiniteGroups.ProcyclicGeneratorIndependence
public import ProfiniteGroups.ProcyclicTorsionFree
public import ProfiniteGroups.ProcyclicBaseMap
public import ProfiniteGroups.PrimewisePadicKernelTransport
public import ProfiniteGroups.ProcyclicInvariant
public import ProfiniteGroups.ProcyclicRealization
public import ProfiniteGroups.ProcyclicHom
public import ProfiniteGroups.ProcyclicPower

/-!
# Profinite groups

The public entry point for the categorical, finite-quotient, free-product,
pro-`p`, and procyclic APIs. It includes the primewise p-adic model, closed
ideals and subgroups, reconstruction from compatible finite-quotient images,
compatible Sylow families and their reconstructed closed subgroups, finite-quotient
conjugacy of closed subgroups, exponent invariants and quotient models, and power images
of procyclic groups. Import this module to use the entire library; import an
individual `ProfiniteGroups.*` module for a smaller dependency closure.

The procyclic classification and power theorems require an explicit
`IsProcyclic` witness. Continuous sections, presentations and product-ideal
statements retain their own hypotheses; the root import does not strengthen
them. No test module is imported here.
-/
