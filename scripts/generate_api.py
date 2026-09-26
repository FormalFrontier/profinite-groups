#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Bounded mixed-kind native doc-gen4 reference for profinite groups.

Adapted by Hive Task hive-request-49578d0143b3fe26e93ee6e54fa1752f1d60bc26,
UID e4f64178-9024-4fe9-8eba-f63c724e7497, from accepted finite-group Tate
cohomology 61577f7cf2e02715f621a724aa692921ab6bbad9, authored by worker-b
Task hive-request-381dc6f93292eb39ea2d5b25f09baacdc8b20d9e,
UID cd8c84f8-2dbf-4399-9c70-1de364ffa99f. Earlier expression comes from
polynomial-root-stability 95ac896f81a3190b2634a4246a3e924d2a267a61
and Anchor's ideal-completion f0c8c34386109116e4912fb425a8ad15d9dc42a4.
Pinned records are documentation input, not proof or release certification.
Wording and lifecycle caveats adapted by worker-b Hive Task
hive-request-1706c2a7c232d243b2552dc0fc1e1b44eac183cd,
UID 20fbc411-a19e-45aa-bf2d-326a3d1ea887; original authorship is unchanged.
"""

if not __debug__:
    raise SystemExit("optimized Python is not supported for API generation")

import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re


TOOL = "97d4ecdfc8e09e7f511724c25e303d448de6a3db"
TOOL_TREE = "ebf77f3e174c145c9ca2db0df1c18a78ae87c93b"
SOURCE = "2417a6348d6abede2cf08f46fbb852a9f3d12d42"
SOURCE_TREE = "0a8a4087cac28d9728c397504051cb53e4c20154"
MODULES = (
    'ProfiniteGroups',
    'ProfiniteGroups.ClosedIdealPi',
    'ProfiniteGroups.ContinuousSection',
    'ProfiniteGroups.EpiMono',
    'ProfiniteGroups.FinitePresentation',
    'ProfiniteGroups.FiniteQuotientHom',
    'ProfiniteGroups.FreeProduct',
    'ProfiniteGroups.PiIdealQuotient',
    'ProfiniteGroups.PrimewisePadic',
    'ProfiniteGroups.PrimewisePadicIdealTransport',
    'ProfiniteGroups.PrimewisePadicIdeals',
    'ProfiniteGroups.PrimewisePadicKernel',
    'ProfiniteGroups.PrimewisePadicKernelTransport',
    'ProfiniteGroups.PrimewisePadicQuotients',
    'ProfiniteGroups.PrimewisePadicSubgroups',
    'ProfiniteGroups.ProP',
    'ProfiniteGroups.Procyclic',
    'ProfiniteGroups.ProcyclicBaseMap',
    'ProfiniteGroups.ProcyclicGeneratorIndependence',
    'ProfiniteGroups.ProcyclicHom',
    'ProfiniteGroups.ProcyclicInvariant',
    'ProfiniteGroups.ProcyclicPower',
    'ProfiniteGroups.ProcyclicQuotient',
    'ProfiniteGroups.ProcyclicRealization',
    'ProfiniteGroups.ProcyclicTorsionFree',
    'ProfiniteGroupsTests',
    'Tests.DirectImports',
    'Tests.PrimewisePadicIdealTransport',
    'Tests.PrimewisePadicKernelTransport',
    'Tests.PrimewisePadicQuotients',
    'Tests.ProcyclicBaseMap',
    'Tests.ProcyclicGeneratorIndependence',
    'Tests.ProcyclicHom',
    'Tests.ProcyclicInvariant',
    'Tests.ProcyclicPower',
    'Tests.ProcyclicQuotient',
    'Tests.ProcyclicRealization',
    'Tests.ProcyclicTorsionFree',
    'Tests.PublicRoot',
)
SOURCE_INPUT_SHA256 = {
    'ProfiniteGroups.lean': '315a12f920f4c153d8a8689caf4a51f158daac5c3d7dada9bf150eb45cacfb47',
    'ProfiniteGroups/ClosedIdealPi.lean': 'fe3f5b2fb3ea47fb55e55630c9724029ac0153b3b4a66caa5d567edc533106bb',
    'ProfiniteGroups/ContinuousSection.lean': '484daa2ff4043061fc038f3b2e039b7fc50e64f53bfe98c9cce691cdbc6dc85e',
    'ProfiniteGroups/EpiMono.lean': '38e6a4c6e039bdb934bce864027ed892e4f1c42f1de6b8cbbc817c0a25fc6b1b',
    'ProfiniteGroups/FinitePresentation.lean': 'd10097494ed2b44f18d01dc1aea05d13148075e5110f86a5650f902f70557aa4',
    'ProfiniteGroups/FiniteQuotientHom.lean': 'c357a175f1183d824e74674ecbce9efcbf363c55b999dadc2286b377f03470e5',
    'ProfiniteGroups/FreeProduct.lean': 'a0fc38078bfb74b86521411e9927295c59b65016ec64324ffed45e5bb3be96af',
    'ProfiniteGroups/PiIdealQuotient.lean': 'b49ca0e411ab891c0a392e4b5556750531bcd17f4629314ed55e67b8809c7b40',
    'ProfiniteGroups/PrimewisePadic.lean': '979c915c1fb81145536412f51e6ea43a99e7ceecf6f4c860390e51b0e544cbe6',
    'ProfiniteGroups/PrimewisePadicIdealTransport.lean': 'a44c6b2cad8d624099c83c0dc9583804ef6ce0682938ab8bde57471ee7136d96',
    'ProfiniteGroups/PrimewisePadicIdeals.lean': '96045517e693a622bf14ae47efe9c1a15ebfc4d016cc380df1b8b2976c63bbe1',
    'ProfiniteGroups/PrimewisePadicKernel.lean': 'c5d3670bf59b38a3386244c81955d5d25fb51334bd4f0c38572b1cc379025134',
    'ProfiniteGroups/PrimewisePadicKernelTransport.lean': 'decd27f193b52ef0e022419e60ccf62b70018ffb79725527c109e7ce28f62978',
    'ProfiniteGroups/PrimewisePadicQuotients.lean': '76e5c991d9930f214df6d95aa9cf37e0ed1db38f6ffb307d47d932b82785f7d3',
    'ProfiniteGroups/PrimewisePadicSubgroups.lean': 'ac5b99e3df2c85a70b678ffb201e687a1fff30ffed4286af87c5c2f186f04752',
    'ProfiniteGroups/ProP.lean': '4d55c1f637817a413aa1e1fe44db5981277f43f32f952497829c776ac00869fa',
    'ProfiniteGroups/Procyclic.lean': '77428ad1fb0656ab008c7ec52be215aa262548d71fe55aaac8ac5dc3b30967c8',
    'ProfiniteGroups/ProcyclicBaseMap.lean': '7ba9b44c17e97b0c3cb2f8f95943a69bd9901c0f29a0c0f3d81a86f2191c635f',
    'ProfiniteGroups/ProcyclicGeneratorIndependence.lean': '28c516c2dc8113d017df815f9b48d4cfe98b854b90866449c73f96e9c0390146',
    'ProfiniteGroups/ProcyclicHom.lean': 'a42a4352f86c6e9ba19bbefb928083b1e2b0277ca2470e7a84d4383353b9e1ca',
    'ProfiniteGroups/ProcyclicInvariant.lean': 'c249fa66f7a13baacf88b7464a5866a2e6e2ad2b0db6319b80546058393e19d7',
    'ProfiniteGroups/ProcyclicPower.lean': 'bc527608f7fe56ab2976d6af3963cffe43fbdf3ae7df7b8e1ace17475fa01aeb',
    'ProfiniteGroups/ProcyclicQuotient.lean': '57695201b165f9ba5386ac000f60085f10356c5baa6e389c4974fd8ffcfd0d06',
    'ProfiniteGroups/ProcyclicRealization.lean': 'a9542a7796554b7a278f7a66af4d351c805ec5c385646754653255225299418a',
    'ProfiniteGroups/ProcyclicTorsionFree.lean': '238402ce46d55e41acbb7c2156ddfe5ec23e6124ae01ce5d8c4f7fe4e409f2c6',
    'ProfiniteGroupsTests.lean': 'eb14f4b3aeeb60aa0f7ee1a45197af89bdd8b525badae44a28bcb5e1e34cdd1d',
    'Tests/DirectImports.lean': 'f39d2016872eefffd03a8ce16f9a069cf7fe895d8403c19b9c41b183725a8258',
    'Tests/PrimewisePadicIdealTransport.lean': 'b4b0bf96fa843fec23e34d89ff21bfaee9ed953d6a6b99df037cbac77439a73a',
    'Tests/PrimewisePadicKernelTransport.lean': '2e98d27b4a7408ce4182dbf13c4675ab74a8daf1f902d1723d8618df98a27790',
    'Tests/PrimewisePadicQuotients.lean': '1f586d364eb164b972808260a9cca3f69f37d7ca87786461258f29221e400958',
    'Tests/ProcyclicBaseMap.lean': '524946bb54f1cc2c59a62092d4873b92084ec2b89fdcb97ddf891b7157e1d336',
    'Tests/ProcyclicGeneratorIndependence.lean': '2e8022d1c6bc3c281d4a65b0e5a674f4b9d598d906acae43aac7b6514fb6383b',
    'Tests/ProcyclicHom.lean': '25e5e04d82b63c9a7e98f88094cd39399cfdedf1a6365c11d101559a4944f7bd',
    'Tests/ProcyclicInvariant.lean': 'c8d25f84071e41b2cb9eeb7773eff45e7902f8ab1fca19c45e786808e5927673',
    'Tests/ProcyclicPower.lean': 'a4729468fccd186c3233b761dc5557aa63965a687edb5670083814b3f55963bb',
    'Tests/ProcyclicQuotient.lean': '0cba5f2bd8bb8e36d8126a7c8a03fba6719aa41f9279f9268a1dae851f27b935',
    'Tests/ProcyclicRealization.lean': '3933502cb3f2d589568b90b40695f0ecb7f17c3a25c884950516b0e8a0d7f3b8',
    'Tests/ProcyclicTorsionFree.lean': 'eabd5eff6e2e769e0e7c9f704233c3f1b7bbcd54d95e8ca5222ee4f177f59fca',
    'Tests/PublicRoot.lean': '550e30490a840e3a1d0f879b9175603ffcf8b145bfc50e05fc9df46ad45e365c',
    'lean-toolchain': '8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88',
    'lakefile.toml': '93f9ea8f1005737c6a2cce6d758d3bd1aa267bdff727f52ce4286ac7c2d5eb52',
    'lake-manifest.json': '8942e073f3e58402683a22f96a61b8e3e1e79c641eb1d12ac627e1d0c45a4bcd',
}
NATIVE_RECORD_SHA256 = {
    'ProfiniteGroups': '9a470405d77c5a3ed6019219c73015091e76a5be36b0165f34b97eb5eef07cac',
    'ProfiniteGroups.ClosedIdealPi': 'f99ce7b6ec86167e8de34b2f849ff498a604ccfeba2a692906a3e2aea88660e6',
    'ProfiniteGroups.ContinuousSection': 'bee4470c4719fa87e273ec2ff35f2bbf3e2c5cf8c70931e7c368d54409ea64ee',
    'ProfiniteGroups.EpiMono': 'd4c137480e067a07316f5194bb8f8d968a779ed63cc69d91614b42e62fc061d4',
    'ProfiniteGroups.FinitePresentation': '5bae02d9d145f135c676cf896afbf754cd0514a840bfa289a68e527976474a06',
    'ProfiniteGroups.FiniteQuotientHom': 'be54f8f0099d7d3f6819d72735908d3f5e9ff67ebe3223931d9efc31bc3b1997',
    'ProfiniteGroups.FreeProduct': 'b5720b9a0a37f6d097ea252c66995c1e9653f3e6371728beb33afedbab83e784',
    'ProfiniteGroups.PiIdealQuotient': 'd2eb097af288daed72a354a47528e2d286b6362234e01f826e73672eaae1b104',
    'ProfiniteGroups.PrimewisePadic': '5f984f2479c1866d8a5cb0cd8a6fd331f2af7be5b6b4d5154530c3d56a735652',
    'ProfiniteGroups.PrimewisePadicIdealTransport': '9ed76a73d37a7ab22e5a47d00ecd642e3c466bd9e64717e0f578a937a4e8becf',
    'ProfiniteGroups.PrimewisePadicIdeals': 'df75066654b3c1bac29c4dccd030775ba744526871567ff8850db3a79281c062',
    'ProfiniteGroups.PrimewisePadicKernel': '8bedef8094d2c2195e29d0a4d86a8d7a8431c872ac555c996a9809215cd9f336',
    'ProfiniteGroups.PrimewisePadicKernelTransport': 'c4879c8611f5ce1b788cf1c6568c436c5b294c84510014e1c65b28b33dd4ff24',
    'ProfiniteGroups.PrimewisePadicQuotients': '36ac81ef288c4aad29ad9306a8af57c39cb3b02345e867c80aa8d31d19d87c6e',
    'ProfiniteGroups.PrimewisePadicSubgroups': '50752360ae5ed0368f341405e64efc862d6dda2e3b34826d2c4cac0101dcc14e',
    'ProfiniteGroups.ProP': 'f5ebaefed64d6eb1f0d0fccce59933318195f804661be0d7409c5a7b14884cbb',
    'ProfiniteGroups.Procyclic': '49ce4a777d714cf466944ce3227c13264516bd1ca70a1bab59a4fd04501def59',
    'ProfiniteGroups.ProcyclicBaseMap': 'f8ec60e90bc2f33242f0c270cc0974a2630b0ba3480967526063752091723bfa',
    'ProfiniteGroups.ProcyclicGeneratorIndependence': '8918b0a48ae99e00240e285b702bbe62e65d6f21350f8108cb58ce773e52a6f5',
    'ProfiniteGroups.ProcyclicHom': '512cbf082d5a4e1c12cce3caffed1747f98f404152114d448abf61cbdd9f4f15',
    'ProfiniteGroups.ProcyclicInvariant': 'd9f0e06df36196aa3aad996e2517a4ee1346453a03d5333dfe1417ec815473c5',
    'ProfiniteGroups.ProcyclicPower': '49a1291dca14c01a1b6aa2a057b320d0d288d028754b2530338942a60dd422f8',
    'ProfiniteGroups.ProcyclicQuotient': 'be947fded2baf36ac63af6683682e86e37550785a5acc3303bf3329ef4dfbb5e',
    'ProfiniteGroups.ProcyclicRealization': 'd9408747228169396b28d53fb7355e4a3fd1299f3e29cb5a0860c891e45c3803',
    'ProfiniteGroups.ProcyclicTorsionFree': 'fad96bf92ea86b017c01a6445ad77b86a6a0f38a726498d2b0d86b0ea43bed4b',
    'ProfiniteGroupsTests': '50b5edfbffd0aeecb4a13cb777dc4d0917d17b993d450dd35c5170b47099b591',
    'Tests.DirectImports': 'c7e938f4312ecfab1c27b4c4a2f447625d2fdc88196a8521ac569e79a2adbd86',
    'Tests.PrimewisePadicIdealTransport': 'ce279544c63d5a732d18a9fcc8a876af16dedfe94796b745e4b1ac821b1a8482',
    'Tests.PrimewisePadicKernelTransport': '4f92db07788a310d4d2fbdb0c62252d451e0304503c04eeda0b24dc21ae04364',
    'Tests.PrimewisePadicQuotients': 'b484925fdb0b226ccae1c89050bd5beeb8f16e910018ac10bc1c43833a0349b4',
    'Tests.ProcyclicBaseMap': '1028305f3d8f5e01dbec95916233ed0d6f5ae311d0befae5cfc2800eedd3b0c6',
    'Tests.ProcyclicGeneratorIndependence': '84dfdeb826d3482b811892dbeb827563d1ebbc51bd4a213eded8f7490bdc36aa',
    'Tests.ProcyclicHom': 'f3f3b0052ecee2ec999348c81d5e2e1bee67756bca57470cf4ff840734b56b05',
    'Tests.ProcyclicInvariant': '8e0ff29ca0c7aa6abe2f9dd2ac65dd723f657799e08d6cb0802c5749b60d2ac8',
    'Tests.ProcyclicPower': '566b45ee7fa20f5d6f196af22cf63146e929b3acde5cc346b94849209b4d9f13',
    'Tests.ProcyclicQuotient': '0b30da1670e9d88ac5c1bee6f4d537385e84c9cf8afc8bfa6e7f957573ec029d',
    'Tests.ProcyclicRealization': '33c5faf4260a2b295bc67dfbdfe2ed2165ffc270f04464780eca4c4f996abb7a',
    'Tests.ProcyclicTorsionFree': 'bbc80dba7db2c22d6cc3c1b890d65533aa7efc6b8f4e86feaed52b26b174cb1f',
    'Tests.PublicRoot': 'b5462be20cdaf74e9e0bc57acd0f58d41ea5ea61a5cb446a90e26e0aa8d7f332',
}
COUNTS = {
    'ProfiniteGroups': 0,
    'ProfiniteGroups.ClosedIdealPi': 1,
    'ProfiniteGroups.ContinuousSection': 10,
    'ProfiniteGroups.EpiMono': 3,
    'ProfiniteGroups.FinitePresentation': 29,
    'ProfiniteGroups.FiniteQuotientHom': 36,
    'ProfiniteGroups.FreeProduct': 47,
    'ProfiniteGroups.PiIdealQuotient': 13,
    'ProfiniteGroups.PrimewisePadic': 18,
    'ProfiniteGroups.PrimewisePadicIdealTransport': 20,
    'ProfiniteGroups.PrimewisePadicIdeals': 20,
    'ProfiniteGroups.PrimewisePadicKernel': 9,
    'ProfiniteGroups.PrimewisePadicKernelTransport': 4,
    'ProfiniteGroups.PrimewisePadicQuotients': 30,
    'ProfiniteGroups.PrimewisePadicSubgroups': 34,
    'ProfiniteGroups.ProP': 69,
    'ProfiniteGroups.Procyclic': 44,
    'ProfiniteGroups.ProcyclicBaseMap': 12,
    'ProfiniteGroups.ProcyclicGeneratorIndependence': 4,
    'ProfiniteGroups.ProcyclicHom': 15,
    'ProfiniteGroups.ProcyclicInvariant': 9,
    'ProfiniteGroups.ProcyclicPower': 30,
    'ProfiniteGroups.ProcyclicQuotient': 19,
    'ProfiniteGroups.ProcyclicRealization': 21,
    'ProfiniteGroups.ProcyclicTorsionFree': 5,
    'ProfiniteGroupsTests': 0,
    'Tests.DirectImports': 6,
    'Tests.PrimewisePadicIdealTransport': 1,
    'Tests.PrimewisePadicKernelTransport': 26,
    'Tests.PrimewisePadicQuotients': 2,
    'Tests.ProcyclicBaseMap': 5,
    'Tests.ProcyclicGeneratorIndependence': 1,
    'Tests.ProcyclicHom': 26,
    'Tests.ProcyclicInvariant': 16,
    'Tests.ProcyclicPower': 15,
    'Tests.ProcyclicQuotient': 4,
    'Tests.ProcyclicRealization': 26,
    'Tests.ProcyclicTorsionFree': 0,
    'Tests.PublicRoot': 18,
}
KINDS = ("def", "theorem", "instance", "structure", "class", "ctor")
DOC_LINK_OVERRIDES = {
    ("Tests.PrimewisePadicIdealTransport", "instFactPrimeValNat_tests"):
        "Tests.PrimewisePadicQuotients",
    ("ProfiniteGroups.PrimewisePadicQuotients", "ProfiniteGrp.instFactPrimeValNat_profiniteGroups_3"):
        "ProfiniteGroups.PrimewisePadicSubgroups",
    ("ProfiniteGroups.PrimewisePadicIdealTransport", "ProfiniteGrp.instFactPrimeValNat_profiniteGroups_3"):
        "ProfiniteGroups.PrimewisePadicSubgroups",
    ("ProfiniteGroups.ProcyclicRealization", "ProfiniteGrp.instFactPrimeValNat_profiniteGroups_4"):
        "ProfiniteGroups.ProcyclicTorsionFree",
}
EXPECTED_INSTANCES = {
    'ProfiniteGroups.ContinuousSection': {
        'QuotientGroup.instTotallyDisconnectedSpace': ('TotallyDisconnectedSpace', ('HasQuotient.Quotient',)),
    },
    'ProfiniteGroups.FinitePresentation': {
        'Profinite.FinitePresentation.surjectiveIndex_nonempty': ('Nonempty', ('Profinite.FinitePresentation.SurjectiveIndex',)),
        'Profinite.FinitePresentation.surjectiveIndex_isCodirected': ('IsDirected', ('Profinite.FinitePresentation.SurjectiveIndex',)),
    },
    'ProfiniteGroups.FiniteQuotientHom': {
        'ProfiniteGrp.FiniteQuotientHom.diagramObjDiscreteTopology': ('DiscreteTopology', ('TopCat.carrier',)),
        'ProfiniteGrp.FiniteQuotientHom.instFunLikeHomStageHomHomStage': ('DFunLike', ('ProfiniteGrp.FiniteQuotientHom.HomStageHom', 'ProfiniteGrp.FiniteQuotientHom.HomStage', 'ProfiniteGrp.FiniteQuotientHom.HomStage')),
        'ProfiniteGrp.FiniteQuotientHom.homStageDirectedSystem': ('DirectedSystem', ('ProfiniteGrp.FiniteQuotientHom.HomStage',)),
    },
    'ProfiniteGroups.FreeProduct': {
        'ProfiniteGrp.FreeProduct.AdmissibleQuotient.instPartialOrder': ('PartialOrder', ('ProfiniteGrp.FreeProduct.AdmissibleQuotient',)),
        'ProfiniteGrp.FreeProduct.AdmissibleQuotient.instSemilatticeInf': ('SemilatticeInf', ('ProfiniteGrp.FreeProduct.AdmissibleQuotient',)),
        'ProfiniteGrp.FreeProduct.AdmissibleQuotient.instNonempty': ('Nonempty', ('ProfiniteGrp.FreeProduct.AdmissibleQuotient',)),
    },
    'ProfiniteGroups.ProP': {
        'ProfiniteGrp.MaximalProPQuotient.Quotient.instPartialOrder': ('PartialOrder', ('ProfiniteGrp.MaximalProPQuotient.Quotient',)),
        'ProfiniteGrp.MaximalProPQuotient.Quotient.instSemilatticeInf': ('SemilatticeInf', ('ProfiniteGrp.MaximalProPQuotient.Quotient',)),
        'ProfiniteGrp.MaximalProPQuotient.Quotient.instNonempty': ('Nonempty', ('ProfiniteGrp.MaximalProPQuotient.Quotient',)),
        'ProfiniteGrp.MaximalProPQuotient.Quotient.instOrderTop': ('OrderTop', ('ProfiniteGrp.MaximalProPQuotient.Quotient',)),
        'ProfiniteGrp.MaximalProPQuotient.product_isProP': ('ProfiniteGrp.IsProP', ('ProfiniteGrp.MaximalProPQuotient.product',)),
        'ProfiniteGrp.FreeProPProduct.product_isProP': ('ProfiniteGrp.IsProP', ('ProfiniteGrp.FreeProPProduct.product',)),
    },
    'ProfiniteGroups.ProcyclicPower': {
        'ProfiniteGrp.powerImage_normal': ('Subgroup.Normal', ('ClosedSubgroup.toSubgroup',)),
    },
}
KEY_TOKENS = {
    "ProfiniteGrp.FiniteQuotientHom.stageToContinuousHom_injective":
        ("(F : Type v)", "[TopologicalSpace F]", "(U : StageIndex G)"),
    "ProfiniteGrp.FreeProduct.lift_comp_assoc":
        ("{ι : Type v}", "{Z : ProfiniteGrp.{max u v}}", "(h : Q ⟶ Z)"),
    "ProfiniteGrp.powerImage_index_dvd":
        ("(hG : G.IsProcyclic)", "(hn : 0 < n)", ".index ∣ n"),
    "ProfiniteGrp.isProcyclic_nonempty_continuousMulEquiv_iff_exponents_eq":
        ("(G : ProfiniteGrp.{u})", "(H : ProfiniteGrp.{v})", "(hH : H.IsProcyclic)"),
}
CATALOGUE = {
    "ProfiniteGroups.FiniteQuotientHom": {
        "HomStageHom.mk": "Constructor packaging a function between two finite-quotient Hom stages.",
        "instFunLikeHomStageHomHomStage": "The stage-map bundle acts on stage homomorphisms as a function; equality of the underlying functions determines the bundle.",
    },
    "ProfiniteGroups.FreeProduct": {
        "AdmissibleQuotient.mk": "Constructor combining a finite-index normal subgroup with continuity of its pullback to each factor.",
        "AdmissibleQuotient.ext_iff": "Two admissible quotients are equal exactly when their underlying finite-index normal subgroups agree.",
        "AdmissibleQuotient.ext": "Extensionality reduces equality of admissible quotients to their inherited subgroup field.",
        "AdmissibleQuotient.toFiniteIndexNormalSubgroup": "Projection of an admissible quotient to its finite-index normal subgroup of the abstract free product.",
        "AdmissibleQuotient.isOpen_comap'": "An admissible quotient has an open inverse-image kernel in every profinite factor.",
        "AdmissibleQuotient.instPartialOrder": "Orders admissible quotients through their finite-index normal subgroup order.",
        "AdmissibleQuotient.instSemilatticeInf": "Intersection of admissible quotient kernels supplies their common-refinement infimum.",
        "AdmissibleQuotient.instNonempty": "The indiscrete admissible quotient witnesses nonemptiness of the quotient index category.",
        "hom_ext_iff": "Maps from the free profinite product agree exactly when they agree on every factor injection.",
    },
    "ProfiniteGroups.ProP": {
        "IsProP.mk": "Constructor taking a proof that every open-normal finite quotient is a finite p-group.",
        "IsProP.quotient_isPGroup": "Projection of the pro-p property to an individual open-normal quotient.",
        "Quotient.mk": "Constructor for an open normal subgroup together with its p-group quotient condition.",
        "Quotient.ext_iff": "Equality of eligible p-quotients is characterized by equality of their open normal subgroups.",
        "Quotient.ext": "Extensionality for eligible p-quotients uses their inherited subgroup data.",
        "Quotient.toOpenNormalSubgroup": "Projection from an eligible p-quotient to its open normal subgroup.",
        "Quotient.isPGroup'": "An eligible quotient carries the finite p-group property specified in its structure.",
        "Quotient.instPartialOrder": "Orders the eligible p-quotients through their open normal subgroup order.",
        "Quotient.instSemilatticeInf": "Common refinement by intersection equips eligible p-quotients with infima.",
        "Quotient.instNonempty": "The trivial quotient gives a nonempty eligible p-quotient category.",
        "Quotient.instOrderTop": "The indiscrete open normal subgroup is the top eligible p-quotient.",
        "hom_ext_iff": "Morphisms from the free pro-p product agree if and only if their composites with each canonical factor map agree.",
    },
    "Tests.PrimewisePadicKernelTransport": {
        "commutingSquare": "Checks that universe transport commutes with additive-to-multiplicative comparison.",
        "arbitraryMapKernelMembership": "Membership in the transported kernel ideal is tested by evaluating the map after the corresponding ring universe change.",
        "arbitraryMapIdeal": "Pullback of the kernel ideal along a universe change matches the ideal of the composite map.",
        "arbitraryMapExponents": "Kernel exponents of an arbitrary target map are unchanged by primewise universe transport.",
        "zeroToPositive": "Tests preservation of exponents while transporting a map from universe zero to universe one.",
        "positiveToZero": "Tests pullback of kernel ideals when transporting from universe one to zero.",
        "identityInfinite": "The identity map after universe transport has infinite exponent at each prime.",
        "trivialZero": "The trivial map after universe transport has zero exponent at each prime.",
        "arbitraryElementComparison": "Compares the generator-based exponent family with the actual kernel exponent family without requiring the element to generate.",
        "nongeneratorConstant": "The base map selected by the identity element of the cyclic group of order twelve is constant.",
        "nongeneratorZero": "The identity element's primewise exponent family in that cyclic group is zero.",
        "nongeneratorNotSurjective": "The base map of that nongenerator cannot surject onto the nontrivial cyclic group.",
        "mixedMap_mk": "Checks the evaluation of the mixed-profile map on a represented element.",
        "mixedMap_kernelIdeal": "Checks the kernel ideal computed for the mixed finite/infinite/zero profile map.",
        "mixedKernelIdeal": "Checks the mixed-profile kernel ideal against its coordinate description.",
        "mixedExponent": "Reads off the mixed map's primewise exponent family.",
        "mixedZero": "Tests the zero-exponent coordinate of the mixed map.",
        "mixedFinite": "Tests the finite positive-exponent coordinate of the mixed map.",
        "mixedInfinite": "Tests the infinite-exponent coordinate of the mixed map.",
        "mixedNotTrivial": "The mixed-profile map is not the constant homomorphism.",
        "mixedNotInjective": "A positive finite exponent yields a nontrivial kernel for the mixed map.",
    },
    "Tests.ProcyclicHom": {
        "arbitraryTarget": "Evaluation at a chosen generator characterizes maps even when the target is not procyclic.",
        "evaluationDeterminesMap": "Two maps with the same value on a supplied generator agree.",
        "factorCommutes": "The factorization of a homomorphism through its exponent profile preserves the original map.",
        "surjectionTest": "Under the prescribed-image admissibility condition, the factor map is surjective exactly when that image generates the target.",
        "quotientOrder": "A continuous surjection between procyclic profinite groups exists exactly when every target exponent is at most the corresponding source exponent.",
        "positiveIndependentUniverses": "Checks the factor/base-map commuting equation for source and target in independent positive universes.",
        "finiteProfileQuotient": "Tests the positive finite cyclic quotient profile.",
        "finiteProfileReverseImpossible": "There is no continuous surjection from the order-two model onto the order-four model.",
        "targetIdentityAlways": "The identity of any target group is an admissible image of a generator.",
        "identityNeverSurjectsOntoCyclicTwo": "Sending a generator to the identity cannot surject onto the nontrivial cyclic group of order two.",
        "kleinNotProcyclic": "The Klein four group provides a finite target that is not procyclic.",
        "mapIntoFiniteNoncyclicTarget": "Tests the generator-image criterion for a map into a nonprocyclic finite target.",
        "squareNotSurjective": "The squaring endomorphism on the selected finite cyclic group is not surjective.",
        "squareAdmissible": "Squaring still defines a valid continuous homomorphism without being onto.",
        "squareImageNotOnto": "The image of the squaring map is a proper subgroup in this example.",
        "zeroSourceToZeroTarget": "A zero source exponent permits the specified trivial-target image.",
        "topSourceToArbitrary": "The all-infinite source profile admits a unique continuous homomorphism with any prescribed target element as the image of its generator.",
        "mixedProfileQuotient": "Checks the pointwise admissibility condition for mixed source and target exponents.",
        "identityAndComposition": "Checks composition of the prescribed-generator-image factor maps.",
        "identityEvaluation": "The generator-image construction sends the identity map to the given generator.",
    },
    "Tests.ProcyclicInvariant": {
        "arbitraryGenerators": "Exponents computed from different supplied generators agree.",
        "independentProofs": "The exponent invariant is independent of which procyclicity witness is supplied.",
        "fixedBase": "The chosen base map computes the group exponent family.",
        "forward": "A continuous equivalence preserves the exponent family.",
        "backward": "Equal exponent families construct a continuous group equivalence.",
        "positiveUniverseEquiv": "The equivalence criterion works across independent positive universes.",
        "independentKernel": "Injective postcomposition into a T1 topological group preserves the primewise kernel ideal.",
        "subsingletonZero": "The trivial profinite group has the zero exponent family.",
        "baseMapPrimewiseGenerator": "The canonical primewise image of the integer generator has the expected profile.",
        "primewiseTop": "The unquotiented primewise product has infinite exponent at each prime.",
        "cyclicTwelveCompatibility": "The order-twelve cyclic group's invariant agrees with the exponent family computed from its supplied generator.",
        "cyclicTwoNontrivial": "The cyclic group of order two is not trivial.",
        "cyclicTwoExponentsNonzero": "Its primewise exponent family is not everywhere zero.",
        "cyclicTwoNotEquivalentToSingleton": "The nontrivial cyclic group cannot be continuously equivalent to the singleton group.",
        "primewiseNotEquivalentToSingleton": "The infinite-profile primewise group cannot be continuously equivalent to the singleton group.",
    },
    "Tests.ProcyclicPower": {
        "power_hom_application": "The power map sends a concrete element to its chosen natural-number power.",
        "proof_parameter_independence": "The power image does not depend on the chosen proof of procyclicity.",
        "zero_and_one": "Zero-th and first power images are respectively the bottom and top subgroup.",
        "open_and_divides": "For a positive power the open image has index dividing, not necessarily equal to, the power.",
        "subgroup_generator": "The power of a supplied generator generates the power-image subgroup.",
        "quotient_generator": "Its class generates the finite cyclic quotient by a positive-power image.",
        "all_open": "Every open subgroup is presented by its index-th power image.",
        "subgroup_bridge": "An ordinary open subgroup agrees with the matching power image.",
        "equal_index_unique": "Open subgroups of a procyclic group with the same index are equal.",
        "open_membership": "Membership in a positive-power open image supplies a concrete power root.",
        "two_fourth_index": "Fourth powers in the cyclic group of order two have index two, not four.",
        "three_square_index": "Squares in the cyclic group of order three are surjective and have index one.",
        "four_square_index": "Squares in the cyclic group of order four have index two.",
        "four_square_nontrivial": "The squares in the cyclic group of order four include a nonidentity element.",
        "trivial_power_top": "The seventh-power image of the trivial group is the top subgroup.",
    },
    "Tests.ProcyclicQuotient": {
        "mixedPrimewiseMap_surjective": "A mixed finite/infinite/zero coordinate quotient map is surjective.",
        "mixedPrimewiseMap_kernelIdeal": "The mixed quotient map has the declared primewise kernel ideal.",
    },
    "Tests.ProcyclicRealization": {
        "arbitraryMap": "The canonical realization map is surjective for every primewise exponent family.",
        "arbitraryActualKernel": "The realized map's kernel ideal is the ideal prescribed by its exponent family.",
        "arbitraryExtractedKernel": "The computed kernel exponents of a realization map recover the input family.",
        "arbitraryRepresentative": "Computes each coordinate of the realization map on an arbitrary ring representative.",
        "arbitraryGenerator": "The distinguished image of the integer is a topological generator.",
        "arbitraryInvariant": "The realized group's exponent invariant equals the prescribed family.",
        "arbitraryPositiveUniverseExists": "The realization construction works in a positive universe.",
        "arbitraryIndependentUniverseEquiv": "Equivalent exponent profiles produce models across independent universes.",
        "allZeroKernel": "An all-zero profile has the full primewise ideal as its kernel.",
        "allZeroInvariant": "The corresponding quotient has zero exponent at every prime.",
        "allZeroTrivial": "The all-zero realization is a trivial profinite group.",
        "allTopInvariant": "The all-infinite realization has the infinite exponent profile.",
        "allTopGeneratorCoordinate": "The all-infinite model's canonical generator has the stated coordinate value.",
        "allTopGeneratorNotIdentity": "The all-infinite model's chosen generator is not the identity.",
        "positiveFiniteGeneratorCoordinate": "The finite positive coordinate of the canonical generator has its expected residue.",
        "positiveFiniteInvariant": "A positive finite exponent contributes that exact primewise invariant.",
        "positiveFiniteGeneratorNotIdentity": "The positive finite coordinate prevents the canonical generator being the identity.",
        "mixedValues": "The mixed profile assigns respectively zero, finite and infinite coordinate exponents.",
        "mixedZeroCoordinate": "The zero-exponent coordinate of a mixed realization is trivial.",
        "mixedFiniteCoordinate": "The finite positive coordinate has its expected residue model.",
        "mixedTopCoordinate": "The infinite coordinate retains its full p-adic model.",
        "mixedInvariant": "The mixed realization's invariant recovers its full input family.",
        "unequalProfilesNoEquiv": "Different primewise exponent families cannot produce equivalent realized groups.",
    },
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


class Header(HTMLParser):
    """Extract all visible native tokens, including hidden-by-CSS implicits."""

    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.text = []
        self.kinds = []
        self.names = []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected/active native header tag")
        attributes = dict(attrs)
        require(len(attrs) == len(attributes) and set(attributes) <= {"class", "href", "id"},
                "active/unknown native header attribute")
        require(tag == "a" or "href" not in attributes, "unexpected native header link")
        require("id" not in attributes or
                (tag == "span" and re.fullmatch(r"[\w.']+", attributes["id"]) is not None),
                "active/unknown native header id")
        require("href" not in attributes or
                re.fullmatch(r"\./[\w./#'-]+", attributes["href"]) is not None,
                "active/external native header link")
        classes = set(attributes.get("class", "").split())
        if tag == "div" and "decl_type" in classes:
            self.text.append(" ")
        self.stack.append((tag, classes))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError("unexpected native header comment")

    def handle_decl(self, _):
        raise ValueError("unexpected native header declaration")

    def rendered(self):
        return " ".join("".join(self.text).split())


def source_anchor(raw, line, name, doc, kind):
    lines = raw.decode("utf-8").splitlines()
    require(type(line) is int and 0 < line <= len(lines), "invalid native source line: " + name)
    source_line = lines[line - 1]
    around = "\n".join(lines[max(0, line - 12):min(len(lines), line + 14)])
    if doc:
        source_comments = re.findall(r"/--(.*?)-/", around, re.DOTALL)
        require(bool(source_comments), "native source docstring position differs: " + name)
        require(any(comment.strip() == doc.strip() for comment in source_comments),
                "native docstring/source mismatch: " + name)
    else:
        require(kind == "ctor" or not source_line.startswith("/--"),
                "native docstring missing: " + name)
    source_name = name.rsplit(".", 1)[-1].removesuffix("_assoc")
    source_matches = (source_name in around or
                      kind == "ctor" and ("structure " in around or "class " in around) or
                      name.endswith(".toFiniteIndexNormalSubgroup") and
                      "extends FiniteIndexNormalSubgroup" in around or
                      name.endswith(".toOpenNormalSubgroup") and
                      "extends OpenNormalSubgroup" in around or
                      (source_name in {"ext", "ext_iff", "hom_ext_iff"} and
                       "@[ext]" in around) or
                      source_name.startswith("inst") and "instance" in source_line)
    require(source_matches, "native source/name position differs: " + name)


def catalogue_note(module, name, kind):
    short_name = name.rsplit(".", 1)[-1]
    if short_name.startswith("instFactPrime"):
        if "OfNat" in short_name:
            return "A local test instance supplies primality of the concrete prime five for residue computations."
        return "A module-local generated instance supplies primality evidence carried by a prime-indexed value; it is not a public API promise."
    matches = [note for suffix, note in CATALOGUE.get(module, {}).items()
               if name == suffix or name.endswith("." + suffix)]
    require(len(matches) == 1 and kind in KINDS,
            "missing original catalogue explanation: " + name)
    return matches[0]


def check_snapshot(revision, sources):
    require(revision == SOURCE, "unexpected/stale analyzed source revision")
    require(set(sources) == set(SOURCE_INPUT_SHA256), "source/pin inventory differs")
    for path, expected in SOURCE_INPUT_SHA256.items():
        require(digest(sources[path]) == expected, "source/pin drift from accepted input: " + path)


def validate(records, raw_records, sources, revision):
    check_snapshot(revision, sources)
    require(type(records) is dict and type(raw_records) is dict and
            set(records) == set(raw_records) == set(MODULES), "native module inventory differs")
    sections = {"production": {}, "clients": {}}
    undocumented = []
    for module in MODULES:
        record = records[module]
        require(json.loads(raw_records[module]) == record,
                "native record bytes/JSON differ: " + module)
        require(type(record) is dict and set(record) == {"name", "declarations", "instances", "imports"},
                "native module shape differs: " + module)
        require(record["name"] == module, "native module name differs: " + module)
        require(type(record["declarations"]) is list and
                len(record["declarations"]) == COUNTS[module],
                "missing/extra native declaration: " + module)
        require(type(record["instances"]) is list and type(record["imports"]) is list and
                all(type(item) is str for item in record["imports"]) and
                len(set(record["imports"])) == len(record["imports"]),
                "native instances/imports shape differs: " + module)
        instances = {}
        for instance in record["instances"]:
            require(type(instance) is dict and set(instance) == {"name", "className", "typeNames"}
                    and type(instance["name"]) is str and type(instance["className"]) is str
                    and type(instance["typeNames"]) is list and
                    all(type(value) is str for value in instance["typeNames"]),
                    "malformed native instance row: " + module)
            require(instance["name"] not in instances, "duplicate native instance row: " + module)
            instances[instance["name"]] = (instance["className"], tuple(instance["typeNames"]))
        require(instances == EXPECTED_INSTANCES.get(module, {}),
                "missing/extra/wrong native instance table: " + module)
        path = module.replace(".", "/") + ".lean"
        names = set()
        rows = []
        for row in record["declarations"]:
            require(type(row) is dict and set(row) == {"info", "header"}
                    and type(row["info"]) is dict,
                    "native declaration shape differs: " + module)
            info = row["info"]
            require(set(info) == {"name", "kind", "doc", "docLink", "sourceLink", "line"},
                    "native declaration info shape differs: " + module)
            name, kind = info["name"], info["kind"]
            require(type(name) is str and type(kind) is str and kind in KINDS and
                    re.fullmatch(r"[\w.']+", name) is not None,
                    "wrong native name/kind: " + str(name))
            require(name not in names, "duplicate native declaration: " + name)
            names.add(name)
            require(type(info["doc"]) is str and type(row["header"]) is str,
                    "malformed native doc/header: " + name)
            require(info["sourceLink"] == "https://example.invalid/commit/" + revision + "/" + path,
                    "native source module/revision/path differs: " + name)
            doc_module = DOC_LINK_OVERRIDES.get((module, name), module)
            require(info["docLink"] == "./" + doc_module.replace(".", "/") + ".html#" + name,
                    "native self link differs: " + name)
            require("```" not in info["doc"] and
                    re.search(r"<\s*[/!?a-zA-Z][^>\n]*>", info["doc"]) is None,
                    "active/unsupported native docstring: " + name)
            source_anchor(sources[path], info["line"], name, info["doc"], kind)
            header = Header(row["header"])
            visible_kind = "".join(header.kinds)
            signature = header.rendered()
            expected_kinds = ({"def", "abbrev", "noncomputable def", "noncomputable abbrev"}
                              if kind == "def" else {"constructor"} if kind == "ctor" else {kind})
            require(visible_kind in expected_kinds and "".join(header.names) == name and
                    signature.startswith(visible_kind + " " + name + " ") and
                    "```" not in signature,
                    "native signature identity/format differs: " + name)
            for binder in KEY_TOKENS.get(name, ()):
                require(binder in signature, "missing signature binder: " + name + " / " + binder)
            if kind == "instance":
                require(name in instances, "declaration/instance table mismatch: " + name)
            elif name in instances:
                raise ValueError("instance table kind mismatch: " + name)
            note = None
            if not info["doc"]:
                note = catalogue_note(module, name, kind)
                undocumented.append((module, name))
            rows.append(dict(name=name, kind=kind, path=path, line=info["line"],
                             signature=signature, doc=info["doc"].strip(), note=note))
        require(set(instances) == {row["info"]["name"] for row in record["declarations"]
                                   if row["info"]["kind"] == "instance"},
                "missing native instance declaration: " + module)
        require(digest(raw_records[module]) == NATIVE_RECORD_SHA256[module],
                "native raw record differs from pinned tool/input: " + module)
        section = "clients" if module == "ProfiniteGroupsTests" or module.startswith("Tests.") else "production"
        sections[section][module] = (rows, instances)
    require(sum(len(rows) for rows, _ in sections["production"].values()) == 502 and
            sum(len(rows) for rows, _ in sections["clients"].values()) == 146 and
            len(undocumented) == 132,
            "mixed public/client/undocumented inventory differs")
    return sections


def render(records, raw_records, sources, revision):
    sections = validate(records, raw_records, sources, revision)
    lines = ["# Native API reference", "",
             "All 39 shipped Lean modules on pinned Lean `v4.34.0-rc2`, mathlib",
             "`e37d88a26f3791ed5a93daa1f949af1021b8d103` and independent doc-gen4 `" + TOOL + "`.",
             "This is a filtered native reference: 502 production and 146 checked-use",
             "client entries, including structures, a class, constructors, projections,",
             "instances, definitions and theorems. Full native displayed signatures",
             "retain implicit parameters, typeclasses and independent universes.",
             "The source anchors point only to shipped Lean files. Entries without",
             "source docstrings receive clearly marked original catalogue explanations.",
             "The two reexport roots and one test leaf have zero new named entries.",
             "In 23 headers the native pretty-printer displays Lean `⋯`; linked",
             "source statements preserve original unelided source text, not",
             "unabridged elaborated types. The 41 SQLite module-prose rows remain",
             "in shipped Lean source, outside this filtered declaration/instance",
             "index; this is not a full SQLite-table dump.",
             "This is not a census of private declarations or proof fields and does",
             "not certify axioms, proofs, source coverage, rights or release acceptance.",
             "[Reproduction and limitations](README.md).", ""]
    production = []
    clients = []
    instance_rows = []
    for section, heading, target in (("production", "Production API", production),
                                     ("clients", "Checked-use clients", clients)):
        lines.extend(["## " + heading, ""])
        for module in MODULES:
            if module not in sections[section]:
                continue
            rows, instances = sections[section][module]
            lines.extend(["### " + module, "", str(len(rows)) + " native named entries; " +
                          str(len(instances)) + " native instance-table rows.", ""])
            if not rows:
                lines.extend(["No new named declarations in this module.", ""])
            for row in sorted(rows, key=lambda item: (item["line"], item["name"])):
                target.append({"module": module, "name": row["name"], "kind": row["kind"],
                               "line": row["line"]})
                lines.extend(["#### " + row["name"], "", "Kind: `" + row["kind"] + "`.", "",
                              "```lean", row["signature"], "```", ""])
                if row["note"] is None:
                    lines.extend(["**Native source docstring:** " + row["doc"], ""])
                else:
                    lines.extend(["**Original catalogue explanation (not a Lean docstring):** " +
                                  row["note"], ""])
                lines.extend(["[Source](../" + row["path"] + "#L" + str(row["line"]) +
                              ") (native source start line; generated entries may point to their parent).", ""])
            if instances:
                lines.extend(["#### Native instance table", ""])
                for name, (class_name, type_names) in sorted(instances.items()):
                    instance_rows.append(dict(module=module, name=name,
                                              className=class_name, typeNames=list(type_names)))
                    lines.extend(["- `" + name + "`: `" + class_name + "`; type names: " +
                                  (", ".join("`" + value + "`" for value in type_names)
                                   if type_names else "none"), ""])
    markdown = "\n".join(lines).encode("utf-8")
    manifest = dict(format=3, generator="scripts/generate_api.py", docgen_revision=TOOL,
                    docgen_tree=TOOL_TREE, analyzed_source_revision=SOURCE,
                    analyzed_source_tree=SOURCE_TREE, modules=list(MODULES),
                    inputs=SOURCE_INPUT_SHA256, native_record_sha256=NATIVE_RECORD_SHA256,
                    normalized_record_sha256={module: digest(json.dumps(records[module],
                            ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8"))
                            for module in MODULES},
                    production_declarations=production, public_client_declarations=clients,
                    instance_table=instance_rows, undocumented_count=132,
                    api_sha256=digest(markdown), proof_certification=False,
                    release_acceptance=False)
    return markdown, (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-data", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--docgen-revision", required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    require(args.docgen_revision == TOOL, "unexpected/stale doc-gen4 revision")
    root = Path(__file__).resolve().parent.parent
    sources = {}
    for path in SOURCE_INPUT_SHA256:
        source_path = root / path
        require(source_path.is_file() and not source_path.is_symlink(), "missing/linked source input: " + path)
        sources[path] = source_path.read_bytes()
    check_snapshot(args.source_revision, sources)
    actual_lean = {path.relative_to(root).as_posix()
                   for directory in (root, root / "ProfiniteGroups", root / "Tests")
                   for path in directory.glob("*.lean")}
    require(actual_lean == {path for path in SOURCE_INPUT_SHA256 if path.endswith(".lean")},
            "missing/extra shipped Lean module")
    require({path.name for path in root.iterdir()} <= {
        ".git", ".lake", ".gitignore", "LICENSE", "README.md", "formalization.yaml",
        "lean-toolchain", "lakefile.toml", "lake-manifest.json", "ProfiniteGroups.lean",
        "ProfiniteGroupsTests.lean", "ProfiniteGroups", "Tests", "docs", "scripts"},
        "unexpected shipped root file")
    scripts = root / "scripts"
    require(scripts.is_dir() and not scripts.is_symlink() and
            {path.name for path in scripts.iterdir()} ==
            {"generate_api.py", "test_generate_api.py"},
            "unexpected/missing adapter script")
    require(args.native_data.is_dir() and not args.native_data.is_symlink(), "native data directory absent/linked")
    expected_files = {"declaration-data-" + module + ".bmp" for module in MODULES}
    files = set(path.name for path in args.native_data.iterdir())
    require(files == expected_files, "missing/extra native record file")
    raw_records = {}
    records = {}
    for module in MODULES:
        path = args.native_data / ("declaration-data-" + module + ".bmp")
        require(path.is_file() and not path.is_symlink(), "missing/linked native record: " + module)
        raw_records[module] = path.read_bytes()
        records[module] = json.loads(raw_records[module])
    api, manifest = render(records, raw_records, sources, args.source_revision)
    docs = root / "docs"
    require(docs.is_dir() and not docs.is_symlink(), "missing/linked documentation directory")
    expected_docs = {"README.md", "API.md", "api-manifest.json"}
    require({path.name for path in docs.iterdir()} == expected_docs,
            "unexpected/missing documentation file")
    for name, raw in (("API.md", api), ("api-manifest.json", manifest)):
        target = docs / name
        require(not target.is_symlink(), "linked output refused: " + name)
        if args.check:
            require(target.is_file() and target.read_bytes() == raw,
                    "generated file differs/stale manifest: " + name)
    if not args.check:
        (root / "docs" / "API.md").write_bytes(api)
        (root / "docs" / "api-manifest.json").write_bytes(manifest)
    print(json.dumps(dict(status="matched" if args.check else "generated", production=502,
                          clients=146, instances=16, api_sha256=digest(api),
                          proof_certification=False, release_acceptance=False)))


if __name__ == "__main__":
    main()
