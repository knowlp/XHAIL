in_compartment(Experiment,Metabolite,Compartment,Day) :-
  start_compound(Metabolite,Compartment).

in_compartment(Experiment,Metabolite,Compartment,Day) :-
  additional_nutrient(Experiment,Metabolite,Compartment).

in_compartment(Experiment,M1,Compartment,Day) :-
  additional_nutrient(Experiment,M2,Compartment),
  contaminated(M2,M1).

in_compartment(Experiment,"C00255",cytosol,Day) :-
  not exclude(10),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00255",medium,Day),
  catalyst(10,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05437",cytosol,Day) :-
  not exclude(21),
  Day >= 1,
  in_compartment(Experiment,"C05437",medium,Day),
  catalyst(21,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05437",medium,Day) :-
  not exclude(22),
  Day >= 1,
  in_compartment(Experiment,"C05437",cytosol,Day),
  catalyst(22,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01694",cytosol,Day) :-
  not exclude(31),
  Day >= 1,
  in_compartment(Experiment,"C01694",medium,Day),
  catalyst(31,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01694",medium,Day) :-
  not exclude(32),
  Day >= 1,
  in_compartment(Experiment,"C01694",cytosol,Day),
  catalyst(32,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(41),
  Day >= 1,
  in_compartment(Experiment,"C00011",medium,Day),
  catalyst(41,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",medium,Day) :-
  not exclude(42),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  catalyst(42,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",cytosol,Day) :-
  not exclude(51),
  Day >= 1,
  in_compartment(Experiment,"C00007",medium,Day),
  catalyst(51,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",medium,Day) :-
  not exclude(52),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  catalyst(52,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01037",cytosol,Day) :-
  not exclude(91),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C01037",medium,Day),
  catalyst(91,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(92),
  Day >= 1,
  in_compartment(Experiment,"C01037",cytosol,Day),
  catalyst(92,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01037",medium,Day) :-
  not exclude(92),
  Day >= 1,
  in_compartment(Experiment,"C01037",cytosol,Day),
  catalyst(92,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01092",cytosol,Day) :-
  not exclude(101),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C01092",medium,Day),
  catalyst(101,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(102),
  Day >= 1,
  in_compartment(Experiment,"C01092",cytosol,Day),
  catalyst(102,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01092",medium,Day) :-
  not exclude(102),
  Day >= 1,
  in_compartment(Experiment,"C01092",cytosol,Day),
  catalyst(102,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00120",cytosol,Day) :-
  not exclude(111),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00120",medium,Day),
  catalyst(111,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(112),
  Day >= 1,
  in_compartment(Experiment,"C00120",cytosol,Day),
  catalyst(112,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00120",medium,Day) :-
  not exclude(112),
  Day >= 1,
  in_compartment(Experiment,"C00120",cytosol,Day),
  catalyst(112,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(131),
  Day >= 1,
  in_compartment(Experiment,"C00178",medium,Day),
  catalyst(131,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00178",cytosol,Day) :-
  not exclude(131),
  Day >= 1,
  in_compartment(Experiment,"C00178",medium,Day),
  catalyst(131,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00178",medium,Day) :-
  not exclude(132),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00178",cytosol,Day),
  catalyst(132,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00459",cytosol,Day) :-
  not exclude(141),
  Day >= 1,
  in_compartment(Experiment,"C00459",medium,Day),
  catalyst(141,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00459",medium,Day) :-
  not exclude(142),
  Day >= 1,
  in_compartment(Experiment,"C00459",cytosol,Day),
  catalyst(142,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00054",cytosol,Day) :-
  not exclude(151),
  Day >= 1,
  in_compartment(Experiment,"C00054",medium,Day),
  catalyst(151,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00054",medium,Day) :-
  not exclude(152),
  Day >= 1,
  in_compartment(Experiment,"C00054",cytosol,Day),
  catalyst(152,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00378",cytosol,Day) :-
  not exclude(190),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00378",medium,Day),
  catalyst(190,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(230),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  catalyst(230,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(230),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  catalyst(230,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00864",cytosol,Day) :-
  not exclude(241),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00864",medium,Day),
  catalyst(241,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(242),
  Day >= 1,
  in_compartment(Experiment,"C00864",cytosol,Day),
  catalyst(242,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00864",medium,Day) :-
  not exclude(242),
  Day >= 1,
  in_compartment(Experiment,"C00864",cytosol,Day),
  catalyst(242,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(251),
  Day >= 1,
  in_compartment(Experiment,"C01330",medium,Day),
  catalyst(251,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01330",cytosol,Day) :-
  not exclude(251),
  Day >= 1,
  in_compartment(Experiment,"C01330",medium,Day),
  catalyst(251,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01330",medium,Day) :-
  not exclude(252),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C01330",cytosol,Day),
  catalyst(252,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(261),
  Day >= 1,
  in_compartment(Experiment,"C00026",medium,Day),
  in_compartment(Experiment,"C00080",medium,Day),
  catalyst(261,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",medium,Day) :-
  not exclude(262),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  catalyst(262,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(262),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  catalyst(262,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00122",cytosol,Day) :-
  not exclude(321),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00122",medium,Day),
  catalyst(321,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(322),
  Day >= 1,
  in_compartment(Experiment,"C00122",cytosol,Day),
  catalyst(322,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00122",medium,Day) :-
  not exclude(322),
  Day >= 1,
  in_compartment(Experiment,"C00122",cytosol,Day),
  catalyst(322,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(341),
  Day >= 1,
  in_compartment(Experiment,"C00009",medium,Day),
  in_compartment(Experiment,"C00080",medium,Day),
  catalyst(341,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",medium,Day) :-
  not exclude(342),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  catalyst(342,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(342),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  catalyst(342,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00059",cytosol,Day) :-
  not exclude(350),
  Day >= 1,
  in_compartment(Experiment,"C00059",medium,Day),
  catalyst(350,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00238",cytosol,Day) :-
  not exclude(361),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00238",medium,Day),
  catalyst(361,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(362),
  Day >= 1,
  in_compartment(Experiment,"C00238",cytosol,Day),
  catalyst(362,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00238",medium,Day) :-
  not exclude(362),
  Day >= 1,
  in_compartment(Experiment,"C00238",cytosol,Day),
  catalyst(362,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(371),
  Day >= 1,
  in_compartment(Experiment,"C00014",medium,Day),
  catalyst(371,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",medium,Day) :-
  not exclude(372),
  Day >= 1,
  in_compartment(Experiment,"C00014",cytosol,Day),
  catalyst(372,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(390),
  Day >= 1,
  in_compartment(Experiment,"C00022",medium,Day),
  in_compartment(Experiment,"C00080",medium,Day),
  catalyst(390,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",cytosol,Day) :-
  not exclude(401),
  Day >= 1,
  in_compartment(Experiment,"C00042",medium,Day),
  in_compartment(Experiment,"C00080",medium,Day),
  catalyst(401,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",medium,Day) :-
  not exclude(402),
  Day >= 1,
  in_compartment(Experiment,"C00042",cytosol,Day),
  catalyst(402,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(402),
  Day >= 1,
  in_compartment(Experiment,"C00042",cytosol,Day),
  catalyst(402,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00262",cytosol,Day) :-
  not exclude(451),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00262",medium,Day),
  catalyst(451,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(452),
  Day >= 1,
  in_compartment(Experiment,"C00262",cytosol,Day),
  catalyst(452,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00262",medium,Day) :-
  not exclude(452),
  Day >= 1,
  in_compartment(Experiment,"C00262",cytosol,Day),
  catalyst(452,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00526",cytosol,Day) :-
  not exclude(460),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00526",medium,Day),
  catalyst(460,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00330",cytosol,Day) :-
  not exclude(490),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00330",medium,Day),
  catalyst(490,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00214",cytosol,Day) :-
  not exclude(510),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00214",medium,Day),
  catalyst(510,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00475",cytosol,Day) :-
  not exclude(530),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00475",medium,Day),
  catalyst(530,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00299",cytosol,Day) :-
  not exclude(540),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00299",medium,Day),
  catalyst(540,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00387",cytosol,Day) :-
  not exclude(550),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00387",medium,Day),
  catalyst(550,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00212",cytosol,Day) :-
  not exclude(560),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00212",medium,Day),
  catalyst(560,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00242",cytosol,Day) :-
  not exclude(581),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00242",medium,Day),
  catalyst(581,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(582),
  Day >= 1,
  in_compartment(Experiment,"C00242",cytosol,Day),
  catalyst(582,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00242",medium,Day) :-
  not exclude(582),
  Day >= 1,
  in_compartment(Experiment,"C00242",cytosol,Day),
  catalyst(582,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00147",cytosol,Day) :-
  not exclude(590),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00147",medium,Day),
  catalyst(590,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00380",cytosol,Day) :-
  not exclude(600),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00380",medium,Day),
  catalyst(600,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00012",cytosol,Day) :-
  not exclude(630),
  Day >= 1,
  in_compartment(Experiment,"C00012",medium,Day),
  in_compartment(Experiment,"C00080",medium,Day),
  catalyst(630,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00107",cytosol,Day) :-
  not exclude(650),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00107",medium,Day),
  catalyst(650,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00134",cytosol,Day) :-
  not exclude(670),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00134",medium,Day),
  catalyst(670,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00430",cytosol,Day) :-
  not exclude(690),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00430",medium,Day),
  catalyst(690,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00334",cytosol,Day) :-
  not exclude(730),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00334",medium,Day),
  catalyst(730,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"MMET",cytosol,Day) :-
  not exclude(750),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"MMET",medium,Day),
  catalyst(750,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00065",cytosol,Day) :-
  not exclude(781),
  Day >= 1,
  in_compartment(Experiment,"C00065",medium,Day),
  in_compartment(Experiment,"C00080",medium,Day),
  catalyst(781,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00065",medium,Day) :-
  not exclude(782),
  Day >= 1,
  in_compartment(Experiment,"C00065",cytosol,Day),
  catalyst(782,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(782),
  Day >= 1,
  in_compartment(Experiment,"C00065",cytosol,Day),
  catalyst(782,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00183",cytosol,Day) :-
  not exclude(791),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00183",medium,Day),
  catalyst(791,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(792),
  Day >= 1,
  in_compartment(Experiment,"C00183",cytosol,Day),
  catalyst(792,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00183",medium,Day) :-
  not exclude(792),
  Day >= 1,
  in_compartment(Experiment,"C00183",cytosol,Day),
  catalyst(792,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00082",cytosol,Day) :-
  not exclude(801),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00082",medium,Day),
  catalyst(801,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(802),
  Day >= 1,
  in_compartment(Experiment,"C00082",cytosol,Day),
  catalyst(802,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00082",medium,Day) :-
  not exclude(802),
  Day >= 1,
  in_compartment(Experiment,"C00082",cytosol,Day),
  catalyst(802,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00078",cytosol,Day) :-
  not exclude(811),
  Day >= 1,
  in_compartment(Experiment,"C00078",medium,Day),
  in_compartment(Experiment,"C00080",medium,Day),
  catalyst(811,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00078",medium,Day) :-
  not exclude(812),
  Day >= 1,
  in_compartment(Experiment,"C00078",cytosol,Day),
  catalyst(812,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(812),
  Day >= 1,
  in_compartment(Experiment,"C00078",cytosol,Day),
  catalyst(812,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00148",cytosol,Day) :-
  not exclude(821),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00148",medium,Day),
  catalyst(821,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(822),
  Day >= 1,
  in_compartment(Experiment,"C00148",cytosol,Day),
  catalyst(822,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00148",medium,Day) :-
  not exclude(822),
  Day >= 1,
  in_compartment(Experiment,"C00148",cytosol,Day),
  catalyst(822,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00079",cytosol,Day) :-
  not exclude(831),
  Day >= 1,
  in_compartment(Experiment,"C00079",medium,Day),
  in_compartment(Experiment,"C00080",medium,Day),
  catalyst(831,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00079",medium,Day) :-
  not exclude(832),
  Day >= 1,
  in_compartment(Experiment,"C00079",cytosol,Day),
  catalyst(832,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(832),
  Day >= 1,
  in_compartment(Experiment,"C00079",cytosol,Day),
  catalyst(832,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00073",cytosol,Day) :-
  not exclude(841),
  Day >= 1,
  in_compartment(Experiment,"C00073",medium,Day),
  in_compartment(Experiment,"C00080",medium,Day),
  catalyst(841,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00073",medium,Day) :-
  not exclude(842),
  Day >= 1,
  in_compartment(Experiment,"C00073",cytosol,Day),
  catalyst(842,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(842),
  Day >= 1,
  in_compartment(Experiment,"C00073",cytosol,Day),
  catalyst(842,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00407",cytosol,Day) :-
  not exclude(861),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00407",medium,Day),
  catalyst(861,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(862),
  Day >= 1,
  in_compartment(Experiment,"C00407",cytosol,Day),
  catalyst(862,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00407",medium,Day) :-
  not exclude(862),
  Day >= 1,
  in_compartment(Experiment,"C00407",cytosol,Day),
  catalyst(862,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00135",cytosol,Day) :-
  not exclude(871),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00135",medium,Day),
  catalyst(871,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(872),
  Day >= 1,
  in_compartment(Experiment,"C00135",cytosol,Day),
  catalyst(872,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00135",medium,Day) :-
  not exclude(872),
  Day >= 1,
  in_compartment(Experiment,"C00135",cytosol,Day),
  catalyst(872,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00064",cytosol,Day) :-
  not exclude(881),
  Day >= 1,
  in_compartment(Experiment,"C00064",medium,Day),
  in_compartment(Experiment,"C00080",medium,Day),
  catalyst(881,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00064",medium,Day) :-
  not exclude(882),
  Day >= 1,
  in_compartment(Experiment,"C00064",cytosol,Day),
  catalyst(882,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(882),
  Day >= 1,
  in_compartment(Experiment,"C00064",cytosol,Day),
  catalyst(882,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00097",cytosol,Day) :-
  not exclude(901),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00097",medium,Day),
  catalyst(901,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(902),
  Day >= 1,
  in_compartment(Experiment,"C00097",cytosol,Day),
  catalyst(902,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00097",medium,Day) :-
  not exclude(902),
  Day >= 1,
  in_compartment(Experiment,"C00097",cytosol,Day),
  catalyst(902,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00049",cytosol,Day) :-
  not exclude(911),
  Day >= 1,
  in_compartment(Experiment,"C00049",medium,Day),
  in_compartment(Experiment,"C00080",medium,Day),
  catalyst(911,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00049",medium,Day) :-
  not exclude(912),
  Day >= 1,
  in_compartment(Experiment,"C00049",cytosol,Day),
  catalyst(912,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(912),
  Day >= 1,
  in_compartment(Experiment,"C00049",cytosol,Day),
  catalyst(912,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00152",cytosol,Day) :-
  not exclude(921),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00152",medium,Day),
  catalyst(921,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(922),
  Day >= 1,
  in_compartment(Experiment,"C00152",cytosol,Day),
  catalyst(922,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00152",medium,Day) :-
  not exclude(922),
  Day >= 1,
  in_compartment(Experiment,"C00152",cytosol,Day),
  catalyst(922,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00062",cytosol,Day) :-
  not exclude(931),
  Day >= 1,
  in_compartment(Experiment,"C00062",medium,Day),
  in_compartment(Experiment,"C00080",medium,Day),
  catalyst(931,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00062",medium,Day) :-
  not exclude(932),
  Day >= 1,
  in_compartment(Experiment,"C00062",cytosol,Day),
  catalyst(932,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(932),
  Day >= 1,
  in_compartment(Experiment,"C00062",cytosol,Day),
  catalyst(932,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00041",cytosol,Day) :-
  not exclude(941),
  Day >= 1,
  in_compartment(Experiment,"C00041",medium,Day),
  in_compartment(Experiment,"C00080",medium,Day),
  catalyst(941,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00041",medium,Day) :-
  not exclude(942),
  Day >= 1,
  in_compartment(Experiment,"C00041",cytosol,Day),
  catalyst(942,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(942),
  Day >= 1,
  in_compartment(Experiment,"C00041",cytosol,Day),
  catalyst(942,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00121",cytosol,Day) :-
  not exclude(970),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00121",medium,Day),
  catalyst(970,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01684",cytosol,Day) :-
  not exclude(980),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C01684",medium,Day),
  catalyst(980,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"NAG",cytosol,Day) :-
  not exclude(990),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"NAG",medium,Day),
  catalyst(990,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05402",cytosol,Day) :-
  not exclude(1000),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C05402",medium,Day),
  catalyst(1000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00392",cytosol,Day) :-
  not exclude(1010),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00392",medium,Day),
  catalyst(1010,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00256",cytosol,Day) :-
  not exclude(1021),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00256",medium,Day),
  catalyst(1021,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(1022),
  Day >= 1,
  in_compartment(Experiment,"C00256",cytosol,Day),
  catalyst(1022,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00256",medium,Day) :-
  not exclude(1022),
  Day >= 1,
  in_compartment(Experiment,"C00256",cytosol,Day),
  catalyst(1022,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01811",cytosol,Day) :-
  not exclude(1041),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C01811",medium,Day),
  catalyst(1041,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(1042),
  Day >= 1,
  in_compartment(Experiment,"C01811",cytosol,Day),
  catalyst(1042,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01811",medium,Day) :-
  not exclude(1042),
  Day >= 1,
  in_compartment(Experiment,"C01811",cytosol,Day),
  catalyst(1042,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01722",cytosol,Day) :-
  not exclude(1050),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C01722",medium,Day),
  catalyst(1050,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",medium,Day) :-
  not exclude(1111),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00711",medium,Day),
  catalyst(1111,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00711",cytosol,Day) :-
  not exclude(1111),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00711",medium,Day),
  catalyst(1111,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(1112),
  Day >= 1,
  in_compartment(Experiment,"C00026",medium,Day),
  in_compartment(Experiment,"C00711",cytosol,Day),
  catalyst(1112,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00711",medium,Day) :-
  not exclude(1112),
  Day >= 1,
  in_compartment(Experiment,"C00026",medium,Day),
  in_compartment(Experiment,"C00711",cytosol,Day),
  catalyst(1112,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00711",cytosol,Day) :-
  not exclude(1121),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00711",medium,Day),
  catalyst(1121,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(1122),
  Day >= 1,
  in_compartment(Experiment,"C00711",cytosol,Day),
  catalyst(1122,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00711",medium,Day) :-
  not exclude(1122),
  Day >= 1,
  in_compartment(Experiment,"C00711",cytosol,Day),
  catalyst(1122,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00089",cytosol,Day) :-
  not exclude(1130),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00089",medium,Day),
  catalyst(1130,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00095",medium,Day) :-
  not exclude(1140),
  Day >= 1,
  in_compartment(Experiment,"C00089",medium,Day),
  catalyst(1140,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00267",medium,Day) :-
  not exclude(1140),
  Day >= 1,
  in_compartment(Experiment,"C00089",medium,Day),
  catalyst(1140,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00208",cytosol,Day) :-
  not exclude(1150),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00208",medium,Day),
  catalyst(1150,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00137",cytosol,Day) :-
  not exclude(1160),
  Day >= 1,
  in_compartment(Experiment,"C00080",medium,Day),
  in_compartment(Experiment,"C00137",medium,Day),
  catalyst(1160,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(1191),
  Day >= 1,
  in_compartment(Experiment,"C00025",medium,Day),
  catalyst(1191,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",medium,Day) :-
  not exclude(1192),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(1192,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00124",cytosol,Day) :-
  not exclude(1200),
  Day >= 1,
  in_compartment(Experiment,"C00124",medium,Day),
  catalyst(1200,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00093",mitochondrion,Day) :-
  not exclude(1220),
  Day >= 1,
  in_compartment(Experiment,"C00093",cytosol,Day),
  catalyst(1220,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",mitochondrion,Day) :-
  not exclude(1250),
  Day >= 1,
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C00122",mitochondrion,Day),
  catalyst(1250,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00122",cytosol,Day) :-
  not exclude(1250),
  Day >= 1,
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C00122",mitochondrion,Day),
  catalyst(1250,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",mitochondrion,Day) :-
  not exclude(1261),
  Day >= 1,
  in_compartment(Experiment,"C00021",cytosol,Day),
  catalyst(1261,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",cytosol,Day) :-
  not exclude(1262),
  Day >= 1,
  in_compartment(Experiment,"C00021",mitochondrion,Day),
  catalyst(1262,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03722",mitochondrion,Day) :-
  not exclude(1291),
  Day >= 1,
  in_compartment(Experiment,"C03722",cytosol,Day),
  catalyst(1291,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03722",cytosol,Day) :-
  not exclude(1292),
  Day >= 1,
  in_compartment(Experiment,"C03722",mitochondrion,Day),
  catalyst(1292,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00415",mitochondrion,Day) :-
  not exclude(1301),
  Day >= 1,
  in_compartment(Experiment,"C00415",cytosol,Day),
  catalyst(1301,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00415",cytosol,Day) :-
  not exclude(1302),
  Day >= 1,
  in_compartment(Experiment,"C00415",mitochondrion,Day),
  catalyst(1302,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00119",mitochondrion,Day) :-
  not exclude(1311),
  Day >= 1,
  in_compartment(Experiment,"C00119",cytosol,Day),
  catalyst(1311,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00119",cytosol,Day) :-
  not exclude(1312),
  Day >= 1,
  in_compartment(Experiment,"C00119",mitochondrion,Day),
  catalyst(1312,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00147",mitochondrion,Day) :-
  not exclude(1321),
  Day >= 1,
  in_compartment(Experiment,"C00147",cytosol,Day),
  catalyst(1321,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00147",cytosol,Day) :-
  not exclude(1322),
  Day >= 1,
  in_compartment(Experiment,"C00147",mitochondrion,Day),
  catalyst(1322,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01134",mitochondrion,Day) :-
  not exclude(1331),
  Day >= 1,
  in_compartment(Experiment,"C01134",cytosol,Day),
  catalyst(1331,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01134",cytosol,Day) :-
  not exclude(1332),
  Day >= 1,
  in_compartment(Experiment,"C01134",mitochondrion,Day),
  catalyst(1332,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00416",mitochondrion,Day) :-
  not exclude(1341),
  Day >= 1,
  in_compartment(Experiment,"C00416",cytosol,Day),
  catalyst(1341,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00416",cytosol,Day) :-
  not exclude(1342),
  Day >= 1,
  in_compartment(Experiment,"C00416",mitochondrion,Day),
  catalyst(1342,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00418",mitochondrion,Day) :-
  not exclude(1351),
  Day >= 1,
  in_compartment(Experiment,"C00418",cytosol,Day),
  catalyst(1351,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00418",cytosol,Day) :-
  not exclude(1352),
  Day >= 1,
  in_compartment(Experiment,"C00418",mitochondrion,Day),
  catalyst(1352,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01909",mitochondrion,Day) :-
  not exclude(1371),
  Day >= 1,
  in_compartment(Experiment,"C01909",cytosol,Day),
  catalyst(1371,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01909",cytosol,Day) :-
  not exclude(1372),
  Day >= 1,
  in_compartment(Experiment,"C01909",mitochondrion,Day),
  catalyst(1372,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00255",mitochondrion,Day) :-
  not exclude(1381),
  Day >= 1,
  in_compartment(Experiment,"C00255",cytosol,Day),
  catalyst(1381,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00255",cytosol,Day) :-
  not exclude(1382),
  Day >= 1,
  in_compartment(Experiment,"C00255",mitochondrion,Day),
  catalyst(1382,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"OIVAL",mitochondrion,Day) :-
  not exclude(1411),
  Day >= 1,
  in_compartment(Experiment,"OIVAL",cytosol,Day),
  catalyst(1411,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"OIVAL",cytosol,Day) :-
  not exclude(1412),
  Day >= 1,
  in_compartment(Experiment,"OIVAL",mitochondrion,Day),
  catalyst(1412,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00077",mitochondrion,Day) :-
  not exclude(1431),
  Day >= 1,
  in_compartment(Experiment,"C00077",cytosol,Day),
  in_compartment(Experiment,"C00080",mitochondrion,Day),
  catalyst(1431,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00077",cytosol,Day) :-
  not exclude(1432),
  Day >= 1,
  in_compartment(Experiment,"C00077",mitochondrion,Day),
  catalyst(1432,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",mitochondrion,Day) :-
  not exclude(1432),
  Day >= 1,
  in_compartment(Experiment,"C00077",mitochondrion,Day),
  catalyst(1432,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",mitochondrion,Day) :-
  not exclude(1451),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(1451,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",mitochondrion,Day) :-
  not exclude(1451),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(1451,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(1452),
  Day >= 1,
  in_compartment(Experiment,"C00025",mitochondrion,Day),
  in_compartment(Experiment,"C00080",mitochondrion,Day),
  catalyst(1452,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00158",mitochondrion,Day) :-
  not exclude(1491),
  Day >= 1,
  in_compartment(Experiment,"C00158",cytosol,Day),
  in_compartment(Experiment,"C00311",mitochondrion,Day),
  catalyst(1491,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00311",cytosol,Day) :-
  not exclude(1491),
  Day >= 1,
  in_compartment(Experiment,"C00158",cytosol,Day),
  in_compartment(Experiment,"C00311",mitochondrion,Day),
  catalyst(1491,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00158",cytosol,Day) :-
  not exclude(1492),
  Day >= 1,
  in_compartment(Experiment,"C00158",mitochondrion,Day),
  in_compartment(Experiment,"C00311",cytosol,Day),
  catalyst(1492,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00311",mitochondrion,Day) :-
  not exclude(1492),
  Day >= 1,
  in_compartment(Experiment,"C00158",mitochondrion,Day),
  in_compartment(Experiment,"C00311",cytosol,Day),
  catalyst(1492,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00074",cytosol,Day) :-
  not exclude(1501),
  Day >= 1,
  in_compartment(Experiment,"C00074",mitochondrion,Day),
  in_compartment(Experiment,"C00158",cytosol,Day),
  catalyst(1501,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00158",mitochondrion,Day) :-
  not exclude(1501),
  Day >= 1,
  in_compartment(Experiment,"C00074",mitochondrion,Day),
  in_compartment(Experiment,"C00158",cytosol,Day),
  catalyst(1501,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00074",mitochondrion,Day) :-
  not exclude(1502),
  Day >= 1,
  in_compartment(Experiment,"C00074",cytosol,Day),
  in_compartment(Experiment,"C00158",mitochondrion,Day),
  catalyst(1502,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00158",cytosol,Day) :-
  not exclude(1502),
  Day >= 1,
  in_compartment(Experiment,"C00074",cytosol,Day),
  in_compartment(Experiment,"C00158",mitochondrion,Day),
  catalyst(1502,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00158",mitochondrion,Day) :-
  not exclude(1511),
  Day >= 1,
  in_compartment(Experiment,"C00158",cytosol,Day),
  in_compartment(Experiment,"C00711",mitochondrion,Day),
  catalyst(1511,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00711",cytosol,Day) :-
  not exclude(1511),
  Day >= 1,
  in_compartment(Experiment,"C00158",cytosol,Day),
  in_compartment(Experiment,"C00711",mitochondrion,Day),
  catalyst(1511,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00158",cytosol,Day) :-
  not exclude(1512),
  Day >= 1,
  in_compartment(Experiment,"C00158",mitochondrion,Day),
  in_compartment(Experiment,"C00711",cytosol,Day),
  catalyst(1512,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00711",mitochondrion,Day) :-
  not exclude(1512),
  Day >= 1,
  in_compartment(Experiment,"C00158",mitochondrion,Day),
  in_compartment(Experiment,"C00711",cytosol,Day),
  catalyst(1512,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00036",mitochondrion,Day) :-
  not exclude(1521),
  Day >= 1,
  in_compartment(Experiment,"C00036",cytosol,Day),
  catalyst(1521,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",mitochondrion,Day) :-
  not exclude(1521),
  Day >= 1,
  in_compartment(Experiment,"C00036",cytosol,Day),
  catalyst(1521,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00036",cytosol,Day) :-
  not exclude(1522),
  Day >= 1,
  in_compartment(Experiment,"C00036",mitochondrion,Day),
  in_compartment(Experiment,"C00080",mitochondrion,Day),
  catalyst(1522,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(1531),
  Day >= 1,
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  in_compartment(Experiment,"C00383",cytosol,Day),
  catalyst(1531,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00383",mitochondrion,Day) :-
  not exclude(1531),
  Day >= 1,
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  in_compartment(Experiment,"C00383",cytosol,Day),
  catalyst(1531,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",mitochondrion,Day) :-
  not exclude(1532),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00383",mitochondrion,Day),
  catalyst(1532,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00383",cytosol,Day) :-
  not exclude(1532),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00383",mitochondrion,Day),
  catalyst(1532,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(1540),
  Day >= 1,
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  in_compartment(Experiment,"C00042",cytosol,Day),
  catalyst(1540,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",mitochondrion,Day) :-
  not exclude(1540),
  Day >= 1,
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  in_compartment(Experiment,"C00042",cytosol,Day),
  catalyst(1540,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",cytosol,Day) :-
  not exclude(1561),
  Day >= 1,
  in_compartment(Experiment,"C00042",mitochondrion,Day),
  in_compartment(Experiment,"C00711",cytosol,Day),
  catalyst(1561,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00711",mitochondrion,Day) :-
  not exclude(1561),
  Day >= 1,
  in_compartment(Experiment,"C00042",mitochondrion,Day),
  in_compartment(Experiment,"C00711",cytosol,Day),
  catalyst(1561,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",mitochondrion,Day) :-
  not exclude(1562),
  Day >= 1,
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C00711",mitochondrion,Day),
  catalyst(1562,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00711",cytosol,Day) :-
  not exclude(1562),
  Day >= 1,
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C00711",mitochondrion,Day),
  catalyst(1562,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",mitochondrion,Day) :-
  not exclude(1571),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C01328",mitochondrion,Day),
  catalyst(1571,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(1572),
  Day >= 1,
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  catalyst(1572,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01328",mitochondrion,Day) :-
  not exclude(1572),
  Day >= 1,
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  catalyst(1572,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",mitochondrion,Day) :-
  not exclude(1581),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  catalyst(1581,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",mitochondrion,Day) :-
  not exclude(1581),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  catalyst(1581,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(1582),
  Day >= 1,
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  in_compartment(Experiment,"C00080",mitochondrion,Day),
  catalyst(1582,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(1590),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  catalyst(1590,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",mitochondrion,Day) :-
  not exclude(1590),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  catalyst(1590,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",mitochondrion,Day) :-
  not exclude(1590),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  catalyst(1590,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",mitochondrion,Day) :-
  not exclude(1590),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  catalyst(1590,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00188",cytosol,Day) :-
  not exclude(1611),
  Day >= 1,
  in_compartment(Experiment,"C00188",mitochondrion,Day),
  catalyst(1611,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00188",mitochondrion,Day) :-
  not exclude(1612),
  Day >= 1,
  in_compartment(Experiment,"C00188",cytosol,Day),
  catalyst(1612,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00900",mitochondrion,Day) :-
  not exclude(1641),
  Day >= 1,
  in_compartment(Experiment,"C00900",cytosol,Day),
  catalyst(1641,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00900",cytosol,Day) :-
  not exclude(1642),
  Day >= 1,
  in_compartment(Experiment,"C00900",mitochondrion,Day),
  catalyst(1642,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00033",cytosol,Day) :-
  not exclude(1671),
  Day >= 1,
  in_compartment(Experiment,"C00033",mitochondrion,Day),
  catalyst(1671,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00033",mitochondrion,Day) :-
  not exclude(1672),
  Day >= 1,
  in_compartment(Experiment,"C00033",cytosol,Day),
  catalyst(1672,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00055",cytosol,Day) :-
  not exclude(1681),
  Day >= 1,
  in_compartment(Experiment,"C00055",mitochondrion,Day),
  catalyst(1681,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00055",mitochondrion,Day) :-
  not exclude(1682),
  Day >= 1,
  in_compartment(Experiment,"C00055",cytosol,Day),
  catalyst(1682,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00148",cytosol,Day) :-
  not exclude(1691),
  Day >= 1,
  in_compartment(Experiment,"C00148",mitochondrion,Day),
  catalyst(1691,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00148",mitochondrion,Day) :-
  not exclude(1692),
  Day >= 1,
  in_compartment(Experiment,"C00148",cytosol,Day),
  catalyst(1692,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04236",cytosol,Day) :-
  not exclude(1701),
  Day >= 1,
  in_compartment(Experiment,"C04236",mitochondrion,Day),
  catalyst(1701,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04236",mitochondrion,Day) :-
  not exclude(1702),
  Day >= 1,
  in_compartment(Experiment,"C04236",cytosol,Day),
  catalyst(1702,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00037",cytosol,Day) :-
  not exclude(1721),
  Day >= 1,
  in_compartment(Experiment,"C00037",mitochondrion,Day),
  catalyst(1721,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00037",mitochondrion,Day) :-
  not exclude(1722),
  Day >= 1,
  in_compartment(Experiment,"C00037",cytosol,Day),
  catalyst(1722,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00065",cytosol,Day) :-
  not exclude(1731),
  Day >= 1,
  in_compartment(Experiment,"C00065",mitochondrion,Day),
  catalyst(1731,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00065",mitochondrion,Day) :-
  not exclude(1732),
  Day >= 1,
  in_compartment(Experiment,"C00065",cytosol,Day),
  catalyst(1732,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00143",cytosol,Day) :-
  not exclude(1741),
  Day >= 1,
  in_compartment(Experiment,"C00143",mitochondrion,Day),
  catalyst(1741,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00143",mitochondrion,Day) :-
  not exclude(1742),
  Day >= 1,
  in_compartment(Experiment,"C00143",cytosol,Day),
  catalyst(1742,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00101",cytosol,Day) :-
  not exclude(1751),
  Day >= 1,
  in_compartment(Experiment,"C00101",mitochondrion,Day),
  catalyst(1751,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00101",mitochondrion,Day) :-
  not exclude(1752),
  Day >= 1,
  in_compartment(Experiment,"C00101",cytosol,Day),
  catalyst(1752,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",mitochondrion,Day) :-
  not exclude(1771),
  Day >= 1,
  in_compartment(Experiment,"C00014",cytosol,Day),
  catalyst(1771,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(1772),
  Day >= 1,
  in_compartment(Experiment,"C00014",mitochondrion,Day),
  catalyst(1772,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00469",mitochondrion,Day) :-
  not exclude(1781),
  Day >= 1,
  in_compartment(Experiment,"C00469",cytosol,Day),
  catalyst(1781,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00469",cytosol,Day) :-
  not exclude(1782),
  Day >= 1,
  in_compartment(Experiment,"C00469",mitochondrion,Day),
  catalyst(1782,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(1791),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  catalyst(1791,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(1792),
  Day >= 1,
  in_compartment(Experiment,"C00011",mitochondrion,Day),
  catalyst(1792,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",mitochondrion,Day) :-
  not exclude(1801),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  catalyst(1801,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",cytosol,Day) :-
  not exclude(1802),
  Day >= 1,
  in_compartment(Experiment,"C00007",mitochondrion,Day),
  catalyst(1802,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",mitochondrion,Day) :-
  not exclude(1810),
  Day >= 1,
  in_compartment(Experiment,"C00019",mitochondrion,Day),
  in_compartment(Experiment,"C03226",mitochondrion,Day),
  catalyst(1810,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00390",mitochondrion,Day) :-
  not exclude(1810),
  Day >= 1,
  in_compartment(Experiment,"C00019",mitochondrion,Day),
  in_compartment(Experiment,"C03226",mitochondrion,Day),
  catalyst(1810,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03226",mitochondrion,Day) :-
  not exclude(1820),
  Day >= 1,
  in_compartment(Experiment,"2NPMMB",mitochondrion,Day),
  in_compartment(Experiment,"C00007",mitochondrion,Day),
  catalyst(1820,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"2NPMB",mitochondrion,Day) :-
  not exclude(1840),
  Day >= 1,
  in_compartment(Experiment,"2NPMP",mitochondrion,Day),
  in_compartment(Experiment,"C00007",mitochondrion,Day),
  catalyst(1840,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"2NPMP",cytosol,Day) :-
  not exclude(1850),
  Day >= 1,
  in_compartment(Experiment,"2N6H",cytosol,Day),
  in_compartment(Experiment,"C00019",cytosol,Day),
  catalyst(1850,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",cytosol,Day) :-
  not exclude(1850),
  Day >= 1,
  in_compartment(Experiment,"2N6H",cytosol,Day),
  in_compartment(Experiment,"C00019",cytosol,Day),
  catalyst(1850,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"2N6H",cytosol,Day) :-
  not exclude(1860),
  Day >= 1,
  in_compartment(Experiment,"2NPPP",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  catalyst(1860,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"2NPPP",cytosol,Day) :-
  not exclude(1870),
  Day >= 1,
  in_compartment(Experiment,"N4HBZ",cytosol,Day),
  catalyst(1870,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(1870),
  Day >= 1,
  in_compartment(Experiment,"N4HBZ",cytosol,Day),
  catalyst(1870,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(1880),
  Day >= 1,
  in_compartment(Experiment,"C00156",cytosol,Day),
  in_compartment(Experiment,"C04145",cytosol,Day),
  catalyst(1880,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"N4HBZ",cytosol,Day) :-
  not exclude(1880),
  Day >= 1,
  in_compartment(Experiment,"C00156",cytosol,Day),
  in_compartment(Experiment,"C04145",cytosol,Day),
  catalyst(1880,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(1890),
  Day >= 1,
  in_compartment(Experiment,"C00251",cytosol,Day),
  catalyst(1890,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00156",cytosol,Day) :-
  not exclude(1890),
  Day >= 1,
  in_compartment(Experiment,"C00251",cytosol,Day),
  catalyst(1890,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",cytosol,Day) :-
  not exclude(1900),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C01051",cytosol,Day),
  catalyst(1900,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05778",cytosol,Day) :-
  not exclude(1900),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C01051",cytosol,Day),
  catalyst(1900,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",mitochondrion,Day) :-
  not exclude(1910),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00025",mitochondrion,Day),
  catalyst(1910,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",mitochondrion,Day) :-
  not exclude(1910),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00025",mitochondrion,Day),
  catalyst(1910,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02987",mitochondrion,Day) :-
  not exclude(1910),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00025",mitochondrion,Day),
  catalyst(1910,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(1920),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(1920,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(1920),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(1920,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02987",cytosol,Day) :-
  not exclude(1920),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(1920,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02191",mitochondrion,Day) :-
  not exclude(1940),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C01079",mitochondrion,Day),
  catalyst(1940,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(1950),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C02667",cytosol,Day),
  catalyst(1950,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01079",cytosol,Day) :-
  not exclude(1950),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C02667",cytosol,Day),
  catalyst(1950,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(1960),
  Day >= 1,
  in_compartment(Experiment,"C01051",cytosol,Day),
  catalyst(1960,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02667",cytosol,Day) :-
  not exclude(1960),
  Day >= 1,
  in_compartment(Experiment,"C01051",cytosol,Day),
  catalyst(1960,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01051",cytosol,Day) :-
  not exclude(1970),
  Day >= 1,
  in_compartment(Experiment,"C01024",cytosol,Day),
  catalyst(1970,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",mitochondrion,Day) :-
  not exclude(2000),
  Day >= 1,
  in_compartment(Experiment,"C00037",mitochondrion,Day),
  in_compartment(Experiment,"C00091",mitochondrion,Day),
  catalyst(2000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(2000),
  Day >= 1,
  in_compartment(Experiment,"C00037",mitochondrion,Day),
  in_compartment(Experiment,"C00091",mitochondrion,Day),
  catalyst(2000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00430",mitochondrion,Day) :-
  not exclude(2000),
  Day >= 1,
  in_compartment(Experiment,"C00037",mitochondrion,Day),
  in_compartment(Experiment,"C00091",mitochondrion,Day),
  catalyst(2000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",mitochondrion,Day) :-
  not exclude(2020),
  Day >= 1,
  in_compartment(Experiment,"C00119",mitochondrion,Day),
  in_compartment(Experiment,"C00253",mitochondrion,Day),
  catalyst(2020,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01185",mitochondrion,Day) :-
  not exclude(2020),
  Day >= 1,
  in_compartment(Experiment,"C00119",mitochondrion,Day),
  in_compartment(Experiment,"C00253",mitochondrion,Day),
  catalyst(2020,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",mitochondrion,Day) :-
  not exclude(2031),
  Day >= 1,
  in_compartment(Experiment,"C00153",mitochondrion,Day),
  catalyst(2031,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00253",mitochondrion,Day) :-
  not exclude(2031),
  Day >= 1,
  in_compartment(Experiment,"C00153",mitochondrion,Day),
  catalyst(2031,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00153",mitochondrion,Day) :-
  not exclude(2032),
  Day >= 1,
  in_compartment(Experiment,"C00014",mitochondrion,Day),
  in_compartment(Experiment,"C00253",mitochondrion,Day),
  catalyst(2032,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00242",mitochondrion,Day) :-
  not exclude(2041),
  Day >= 1,
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  in_compartment(Experiment,"C00387",mitochondrion,Day),
  catalyst(2041,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00442",mitochondrion,Day) :-
  not exclude(2041),
  Day >= 1,
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  in_compartment(Experiment,"C00387",mitochondrion,Day),
  catalyst(2041,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",mitochondrion,Day) :-
  not exclude(2042),
  Day >= 1,
  in_compartment(Experiment,"C00242",mitochondrion,Day),
  in_compartment(Experiment,"C00442",mitochondrion,Day),
  catalyst(2042,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00387",mitochondrion,Day) :-
  not exclude(2042),
  Day >= 1,
  in_compartment(Experiment,"C00242",mitochondrion,Day),
  in_compartment(Experiment,"C00442",mitochondrion,Day),
  catalyst(2042,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00147",mitochondrion,Day) :-
  not exclude(2051),
  Day >= 1,
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  in_compartment(Experiment,"C00212",mitochondrion,Day),
  catalyst(2051,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00442",mitochondrion,Day) :-
  not exclude(2051),
  Day >= 1,
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  in_compartment(Experiment,"C00212",mitochondrion,Day),
  catalyst(2051,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",mitochondrion,Day) :-
  not exclude(2052),
  Day >= 1,
  in_compartment(Experiment,"C00147",mitochondrion,Day),
  in_compartment(Experiment,"C00442",mitochondrion,Day),
  catalyst(2052,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00212",mitochondrion,Day) :-
  not exclude(2052),
  Day >= 1,
  in_compartment(Experiment,"C00147",mitochondrion,Day),
  in_compartment(Experiment,"C00442",mitochondrion,Day),
  catalyst(2052,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",mitochondrion,Day) :-
  not exclude(2060),
  Day >= 1,
  in_compartment(Experiment,"C00006",mitochondrion,Day),
  catalyst(2060,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",mitochondrion,Day) :-
  not exclude(2060),
  Day >= 1,
  in_compartment(Experiment,"C00006",mitochondrion,Day),
  catalyst(2060,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",mitochondrion,Day) :-
  not exclude(2070),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  catalyst(2070,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",mitochondrion,Day) :-
  not exclude(2070),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  catalyst(2070,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",mitochondrion,Day) :-
  not exclude(2090),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"NMN",mitochondrion,Day),
  catalyst(2090,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",mitochondrion,Day) :-
  not exclude(2090),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"NMN",mitochondrion,Day),
  catalyst(2090,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",mitochondrion,Day) :-
  not exclude(2100),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C01185",mitochondrion,Day),
  catalyst(2100,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00857",mitochondrion,Day) :-
  not exclude(2100),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C01185",mitochondrion,Day),
  catalyst(2100,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(2110),
  Day >= 1,
  in_compartment(Experiment,"C00119",mitochondrion,Day),
  in_compartment(Experiment,"C03722",mitochondrion,Day),
  catalyst(2110,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",mitochondrion,Day) :-
  not exclude(2110),
  Day >= 1,
  in_compartment(Experiment,"C00119",mitochondrion,Day),
  in_compartment(Experiment,"C03722",mitochondrion,Day),
  catalyst(2110,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01185",mitochondrion,Day) :-
  not exclude(2110),
  Day >= 1,
  in_compartment(Experiment,"C00119",mitochondrion,Day),
  in_compartment(Experiment,"C03722",mitochondrion,Day),
  catalyst(2110,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00242",cytosol,Day) :-
  not exclude(2121),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00387",cytosol,Day),
  catalyst(2121,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00442",cytosol,Day) :-
  not exclude(2121),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00387",cytosol,Day),
  catalyst(2121,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(2122),
  Day >= 1,
  in_compartment(Experiment,"C00242",cytosol,Day),
  in_compartment(Experiment,"C00442",cytosol,Day),
  catalyst(2122,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00387",cytosol,Day) :-
  not exclude(2122),
  Day >= 1,
  in_compartment(Experiment,"C00242",cytosol,Day),
  in_compartment(Experiment,"C00442",cytosol,Day),
  catalyst(2122,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00147",cytosol,Day) :-
  not exclude(2131),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00212",cytosol,Day),
  catalyst(2131,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00442",cytosol,Day) :-
  not exclude(2131),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00212",cytosol,Day),
  catalyst(2131,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(2132),
  Day >= 1,
  in_compartment(Experiment,"C00147",cytosol,Day),
  in_compartment(Experiment,"C00442",cytosol,Day),
  catalyst(2132,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00212",cytosol,Day) :-
  not exclude(2132),
  Day >= 1,
  in_compartment(Experiment,"C00147",cytosol,Day),
  in_compartment(Experiment,"C00442",cytosol,Day),
  catalyst(2132,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00153",cytosol,Day) :-
  not exclude(2140),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  catalyst(2140,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00301",cytosol,Day) :-
  not exclude(2140),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  catalyst(2140,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(2150),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  catalyst(2150,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(2150),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  catalyst(2150,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(2160),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  catalyst(2160,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2160),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  catalyst(2160,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(2170),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00857",cytosol,Day),
  catalyst(2170,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(2170),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00857",cytosol,Day),
  catalyst(2170,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(2170),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00857",cytosol,Day),
  catalyst(2170,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(2180),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01185",cytosol,Day),
  catalyst(2180,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00857",cytosol,Day) :-
  not exclude(2180),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01185",cytosol,Day),
  catalyst(2180,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(2190),
  Day >= 1,
  in_compartment(Experiment,"C00119",cytosol,Day),
  in_compartment(Experiment,"C03722",cytosol,Day),
  catalyst(2190,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(2190),
  Day >= 1,
  in_compartment(Experiment,"C00119",cytosol,Day),
  in_compartment(Experiment,"C03722",cytosol,Day),
  catalyst(2190,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01185",cytosol,Day) :-
  not exclude(2190),
  Day >= 1,
  in_compartment(Experiment,"C00119",cytosol,Day),
  in_compartment(Experiment,"C03722",cytosol,Day),
  catalyst(2190,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(2200),
  Day >= 1,
  in_compartment(Experiment,"C00111",cytosol,Day),
  in_compartment(Experiment,"ISUCC",cytosol,Day),
  catalyst(2200,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03722",cytosol,Day) :-
  not exclude(2200),
  Day >= 1,
  in_compartment(Experiment,"C00111",cytosol,Day),
  in_compartment(Experiment,"ISUCC",cytosol,Day),
  catalyst(2200,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01352",mitochondrion,Day) :-
  not exclude(2210),
  Day >= 1,
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  catalyst(2210,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"ISUCC",cytosol,Day) :-
  not exclude(2210),
  Day >= 1,
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  catalyst(2210,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(2220),
  Day >= 1,
  in_compartment(Experiment,"C00119",cytosol,Day),
  in_compartment(Experiment,"C00253",cytosol,Day),
  catalyst(2220,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01185",cytosol,Day) :-
  not exclude(2220),
  Day >= 1,
  in_compartment(Experiment,"C00119",cytosol,Day),
  in_compartment(Experiment,"C00253",cytosol,Day),
  catalyst(2220,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(2231),
  Day >= 1,
  in_compartment(Experiment,"C00153",cytosol,Day),
  catalyst(2231,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00253",cytosol,Day) :-
  not exclude(2231),
  Day >= 1,
  in_compartment(Experiment,"C00153",cytosol,Day),
  catalyst(2231,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00153",cytosol,Day) :-
  not exclude(2232),
  Day >= 1,
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00253",cytosol,Day),
  catalyst(2232,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00054",cytosol,Day) :-
  not exclude(2240),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  catalyst(2240,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(2240),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  catalyst(2240,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2270),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00882",cytosol,Day),
  catalyst(2270,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(2270),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00882",cytosol,Day),
  catalyst(2270,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",mitochondrion,Day) :-
  not exclude(2280),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C01134",mitochondrion,Day),
  catalyst(2280,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00882",mitochondrion,Day) :-
  not exclude(2280),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C01134",mitochondrion,Day),
  catalyst(2280,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(2290),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01134",cytosol,Day),
  catalyst(2290,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00882",cytosol,Day) :-
  not exclude(2290),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01134",cytosol,Day),
  catalyst(2290,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(2300),
  Day >= 1,
  in_compartment(Experiment,"C04352",cytosol,Day),
  catalyst(2300,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01134",cytosol,Day) :-
  not exclude(2300),
  Day >= 1,
  in_compartment(Experiment,"C04352",cytosol,Day),
  catalyst(2300,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2320),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00864",cytosol,Day),
  catalyst(2320,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03492",cytosol,Day) :-
  not exclude(2320),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00864",cytosol,Day),
  catalyst(2320,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(2330),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00099",cytosol,Day),
  in_compartment(Experiment,"C00522",cytosol,Day),
  catalyst(2330,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(2330),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00099",cytosol,Day),
  in_compartment(Experiment,"C00522",cytosol,Day),
  catalyst(2330,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00864",cytosol,Day) :-
  not exclude(2330),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00099",cytosol,Day),
  in_compartment(Experiment,"C00522",cytosol,Day),
  catalyst(2330,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",mitochondrion,Day) :-
  not exclude(2340),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00966",mitochondrion,Day),
  catalyst(2340,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00522",mitochondrion,Day) :-
  not exclude(2340),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00966",mitochondrion,Day),
  catalyst(2340,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(2350),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00966",cytosol,Day),
  catalyst(2350,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00522",cytosol,Day) :-
  not exclude(2350),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00966",cytosol,Day),
  catalyst(2350,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00101",mitochondrion,Day) :-
  not exclude(2370),
  Day >= 1,
  in_compartment(Experiment,"C00234",mitochondrion,Day),
  in_compartment(Experiment,"C02430",mitochondrion,Day),
  catalyst(2370,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03294",mitochondrion,Day) :-
  not exclude(2370),
  Day >= 1,
  in_compartment(Experiment,"C00234",mitochondrion,Day),
  in_compartment(Experiment,"C02430",mitochondrion,Day),
  catalyst(2370,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(2380),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00143",cytosol,Day),
  catalyst(2380,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00445",cytosol,Day) :-
  not exclude(2380),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00143",cytosol,Day),
  catalyst(2380,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00234",cytosol,Day) :-
  not exclude(2391),
  Day >= 1,
  in_compartment(Experiment,"C00445",cytosol,Day),
  catalyst(2391,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00445",cytosol,Day) :-
  not exclude(2392),
  Day >= 1,
  in_compartment(Experiment,"C00234",cytosol,Day),
  catalyst(2392,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00234",mitochondrion,Day) :-
  not exclude(2401),
  Day >= 1,
  in_compartment(Experiment,"C00445",mitochondrion,Day),
  catalyst(2401,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00445",mitochondrion,Day) :-
  not exclude(2402),
  Day >= 1,
  in_compartment(Experiment,"C00234",mitochondrion,Day),
  catalyst(2402,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2410),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00058",cytosol,Day),
  in_compartment(Experiment,"C00101",cytosol,Day),
  catalyst(2410,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(2410),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00058",cytosol,Day),
  in_compartment(Experiment,"C00101",cytosol,Day),
  catalyst(2410,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00234",cytosol,Day) :-
  not exclude(2410),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00058",cytosol,Day),
  in_compartment(Experiment,"C00101",cytosol,Day),
  catalyst(2410,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(2431),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00143",cytosol,Day),
  catalyst(2431,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00445",cytosol,Day) :-
  not exclude(2431),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00143",cytosol,Day),
  catalyst(2431,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(2432),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00445",cytosol,Day),
  catalyst(2432,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00143",cytosol,Day) :-
  not exclude(2432),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00445",cytosol,Day),
  catalyst(2432,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",mitochondrion,Day) :-
  not exclude(2441),
  Day >= 1,
  in_compartment(Experiment,"C00006",mitochondrion,Day),
  in_compartment(Experiment,"C00143",mitochondrion,Day),
  catalyst(2441,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00445",mitochondrion,Day) :-
  not exclude(2441),
  Day >= 1,
  in_compartment(Experiment,"C00006",mitochondrion,Day),
  in_compartment(Experiment,"C00143",mitochondrion,Day),
  catalyst(2441,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",mitochondrion,Day) :-
  not exclude(2442),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00445",mitochondrion,Day),
  catalyst(2442,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00143",mitochondrion,Day) :-
  not exclude(2442),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00445",mitochondrion,Day),
  catalyst(2442,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",mitochondrion,Day) :-
  not exclude(2450),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00143",mitochondrion,Day),
  catalyst(2450,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00440",mitochondrion,Day) :-
  not exclude(2450),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00143",mitochondrion,Day),
  catalyst(2450,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2461),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00101",cytosol,Day),
  catalyst(2461,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(2461),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00101",cytosol,Day),
  catalyst(2461,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03541",cytosol,Day) :-
  not exclude(2461),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00101",cytosol,Day),
  catalyst(2461,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(2462),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C03541",cytosol,Day),
  catalyst(2462,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(2462),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C03541",cytosol,Day),
  catalyst(2462,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00101",cytosol,Day) :-
  not exclude(2462),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C03541",cytosol,Day),
  catalyst(2462,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",mitochondrion,Day) :-
  not exclude(2480),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00234",mitochondrion,Day),
  catalyst(2480,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",mitochondrion,Day) :-
  not exclude(2480),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00234",mitochondrion,Day),
  catalyst(2480,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00440",mitochondrion,Day) :-
  not exclude(2480),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00234",mitochondrion,Day),
  catalyst(2480,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(2490),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00415",cytosol,Day),
  catalyst(2490,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00101",cytosol,Day) :-
  not exclude(2490),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00415",cytosol,Day),
  catalyst(2490,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",mitochondrion,Day) :-
  not exclude(2500),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00415",mitochondrion,Day),
  catalyst(2500,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00101",mitochondrion,Day) :-
  not exclude(2500),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00415",mitochondrion,Day),
  catalyst(2500,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2510),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00921",cytosol,Day),
  catalyst(2510,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(2510),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00921",cytosol,Day),
  catalyst(2510,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00415",cytosol,Day) :-
  not exclude(2510),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00921",cytosol,Day),
  catalyst(2510,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00921",cytosol,Day) :-
  not exclude(2520),
  Day >= 1,
  in_compartment(Experiment,"C00568",cytosol,Day),
  in_compartment(Experiment,"C01300",cytosol,Day),
  catalyst(2520,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(2530),
  Day >= 1,
  in_compartment(Experiment,"C00568",cytosol,Day),
  in_compartment(Experiment,"C04807",cytosol,Day),
  catalyst(2530,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00921",cytosol,Day) :-
  not exclude(2530),
  Day >= 1,
  in_compartment(Experiment,"C00568",cytosol,Day),
  in_compartment(Experiment,"C04807",cytosol,Day),
  catalyst(2530,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(2540),
  Day >= 1,
  in_compartment(Experiment,"C11355",cytosol,Day),
  catalyst(2540,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00568",cytosol,Day) :-
  not exclude(2540),
  Day >= 1,
  in_compartment(Experiment,"C11355",cytosol,Day),
  catalyst(2540,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(2550),
  Day >= 1,
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00251",cytosol,Day),
  catalyst(2550,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C11355",cytosol,Day) :-
  not exclude(2550),
  Day >= 1,
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00251",cytosol,Day),
  catalyst(2550,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(2560),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01300",cytosol,Day),
  catalyst(2560,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04807",cytosol,Day) :-
  not exclude(2560),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01300",cytosol,Day),
  catalyst(2560,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(2580),
  Day >= 1,
  in_compartment(Experiment,"C05925",cytosol,Day),
  catalyst(2580,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04874",cytosol,Day) :-
  not exclude(2580),
  Day >= 1,
  in_compartment(Experiment,"C05925",cytosol,Day),
  catalyst(2580,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(2590),
  Day >= 1,
  in_compartment(Experiment,"C04895",cytosol,Day),
  catalyst(2590,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04874",cytosol,Day) :-
  not exclude(2590),
  Day >= 1,
  in_compartment(Experiment,"C04895",cytosol,Day),
  catalyst(2590,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00120",cytosol,Day) :-
  not exclude(2621),
  Day >= 1,
  in_compartment(Experiment,"C00097",cytosol,Day),
  in_compartment(Experiment,"C01909",cytosol,Day),
  catalyst(2621,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00097",cytosol,Day) :-
  not exclude(2622),
  Day >= 1,
  in_compartment(Experiment,"C00120",cytosol,Day),
  catalyst(2622,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01909",cytosol,Day) :-
  not exclude(2622),
  Day >= 1,
  in_compartment(Experiment,"C00120",cytosol,Day),
  catalyst(2622,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2631),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C01037",cytosol,Day),
  catalyst(2631,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(2631),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C01037",cytosol,Day),
  catalyst(2631,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01909",cytosol,Day) :-
  not exclude(2631),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C01037",cytosol,Day),
  catalyst(2631,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(2632),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C01909",cytosol,Day),
  catalyst(2632,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(2632),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C01909",cytosol,Day),
  catalyst(2632,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01037",cytosol,Day) :-
  not exclude(2632),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C01909",cytosol,Day),
  catalyst(2632,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01037",cytosol,Day) :-
  not exclude(2641),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C01092",cytosol,Day),
  catalyst(2641,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04425",cytosol,Day) :-
  not exclude(2641),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C01092",cytosol,Day),
  catalyst(2641,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00019",cytosol,Day) :-
  not exclude(2642),
  Day >= 1,
  in_compartment(Experiment,"C01037",cytosol,Day),
  in_compartment(Experiment,"C04425",cytosol,Day),
  catalyst(2642,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01092",cytosol,Day) :-
  not exclude(2642),
  Day >= 1,
  in_compartment(Experiment,"C01037",cytosol,Day),
  in_compartment(Experiment,"C04425",cytosol,Day),
  catalyst(2642,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(2651),
  Day >= 1,
  in_compartment(Experiment,"C00041",cytosol,Day),
  in_compartment(Experiment,"C01063",cytosol,Day),
  catalyst(2651,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(2651),
  Day >= 1,
  in_compartment(Experiment,"C00041",cytosol,Day),
  in_compartment(Experiment,"C01063",cytosol,Day),
  catalyst(2651,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01092",cytosol,Day) :-
  not exclude(2651),
  Day >= 1,
  in_compartment(Experiment,"C00041",cytosol,Day),
  in_compartment(Experiment,"C01063",cytosol,Day),
  catalyst(2651,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00041",cytosol,Day) :-
  not exclude(2652),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C01092",cytosol,Day),
  catalyst(2652,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01063",cytosol,Day) :-
  not exclude(2652),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C01092",cytosol,Day),
  catalyst(2652,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(2660),
  Day >= 1,
  in_compartment(Experiment,"C00083",cytosol,Day),
  catalyst(2660,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(2660),
  Day >= 1,
  in_compartment(Experiment,"C00083",cytosol,Day),
  catalyst(2660,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01063",cytosol,Day) :-
  not exclude(2660),
  Day >= 1,
  in_compartment(Experiment,"C00083",cytosol,Day),
  catalyst(2660,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(2670),
  Day >= 1,
  in_compartment(Experiment,"C00647",cytosol,Day),
  catalyst(2670,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00534",cytosol,Day) :-
  not exclude(2670),
  Day >= 1,
  in_compartment(Experiment,"C00647",cytosol,Day),
  catalyst(2670,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(2691),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C06054",cytosol,Day),
  catalyst(2691,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C06055",cytosol,Day) :-
  not exclude(2691),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C06054",cytosol,Day),
  catalyst(2691,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(2692),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C06055",cytosol,Day),
  catalyst(2692,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C06054",cytosol,Day) :-
  not exclude(2692),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C06055",cytosol,Day),
  catalyst(2692,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00027",cytosol,Day) :-
  not exclude(2711),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00250",cytosol,Day),
  catalyst(2711,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00534",cytosol,Day) :-
  not exclude(2711),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00250",cytosol,Day),
  catalyst(2711,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",cytosol,Day) :-
  not exclude(2712),
  Day >= 1,
  in_compartment(Experiment,"C00027",cytosol,Day),
  in_compartment(Experiment,"C00534",cytosol,Day),
  catalyst(2712,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(2712),
  Day >= 1,
  in_compartment(Experiment,"C00027",cytosol,Day),
  in_compartment(Experiment,"C00534",cytosol,Day),
  catalyst(2712,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00250",cytosol,Day) :-
  not exclude(2712),
  Day >= 1,
  in_compartment(Experiment,"C00027",cytosol,Day),
  in_compartment(Experiment,"C00534",cytosol,Day),
  catalyst(2712,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00027",cytosol,Day) :-
  not exclude(2721),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00314",cytosol,Day),
  catalyst(2721,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00250",cytosol,Day) :-
  not exclude(2721),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00314",cytosol,Day),
  catalyst(2721,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",cytosol,Day) :-
  not exclude(2722),
  Day >= 1,
  in_compartment(Experiment,"C00027",cytosol,Day),
  in_compartment(Experiment,"C00250",cytosol,Day),
  catalyst(2722,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00314",cytosol,Day) :-
  not exclude(2722),
  Day >= 1,
  in_compartment(Experiment,"C00027",cytosol,Day),
  in_compartment(Experiment,"C00250",cytosol,Day),
  catalyst(2722,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00018",cytosol,Day) :-
  not exclude(2731),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00627",cytosol,Day),
  catalyst(2731,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00027",cytosol,Day) :-
  not exclude(2731),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00627",cytosol,Day),
  catalyst(2731,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",cytosol,Day) :-
  not exclude(2732),
  Day >= 1,
  in_compartment(Experiment,"C00018",cytosol,Day),
  in_compartment(Experiment,"C00027",cytosol,Day),
  catalyst(2732,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00627",cytosol,Day) :-
  not exclude(2732),
  Day >= 1,
  in_compartment(Experiment,"C00018",cytosol,Day),
  in_compartment(Experiment,"C00027",cytosol,Day),
  catalyst(2732,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2740),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00250",cytosol,Day),
  catalyst(2740,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00018",cytosol,Day) :-
  not exclude(2740),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00250",cytosol,Day),
  catalyst(2740,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2750),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00534",cytosol,Day),
  catalyst(2750,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00647",cytosol,Day) :-
  not exclude(2750),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00534",cytosol,Day),
  catalyst(2750,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2760),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00314",cytosol,Day),
  catalyst(2760,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00627",cytosol,Day) :-
  not exclude(2760),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00314",cytosol,Day),
  catalyst(2760,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(2780),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00061",cytosol,Day),
  catalyst(2780,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00016",cytosol,Day) :-
  not exclude(2780),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00061",cytosol,Day),
  catalyst(2780,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",mitochondrion,Day) :-
  not exclude(2790),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00255",mitochondrion,Day),
  catalyst(2790,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00061",mitochondrion,Day) :-
  not exclude(2790),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00255",mitochondrion,Day),
  catalyst(2790,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2800),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00255",cytosol,Day),
  catalyst(2800,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00061",cytosol,Day) :-
  not exclude(2800),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00255",cytosol,Day),
  catalyst(2800,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(2820),
  Day >= 1,
  in_compartment(Experiment,"A6RP",cytosol,Day),
  in_compartment(Experiment,"DB4P",cytosol,Day),
  catalyst(2820,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04332",cytosol,Day) :-
  not exclude(2820),
  Day >= 1,
  in_compartment(Experiment,"A6RP",cytosol,Day),
  in_compartment(Experiment,"DB4P",cytosol,Day),
  catalyst(2820,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00058",cytosol,Day) :-
  not exclude(2830),
  Day >= 1,
  in_compartment(Experiment,"C00199",cytosol,Day),
  catalyst(2830,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"DB4P",cytosol,Day) :-
  not exclude(2830),
  Day >= 1,
  in_compartment(Experiment,"C00199",cytosol,Day),
  catalyst(2830,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"A6RP",cytosol,Day) :-
  not exclude(2840),
  Day >= 1,
  in_compartment(Experiment,"C04454",cytosol,Day),
  catalyst(2840,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(2840),
  Day >= 1,
  in_compartment(Experiment,"C04454",cytosol,Day),
  catalyst(2840,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(2860),
  Day >= 1,
  in_compartment(Experiment,"C01304",cytosol,Day),
  catalyst(2860,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01268",cytosol,Day) :-
  not exclude(2860),
  Day >= 1,
  in_compartment(Experiment,"C01304",cytosol,Day),
  catalyst(2860,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2891),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01081",cytosol,Day),
  catalyst(2891,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00068",cytosol,Day) :-
  not exclude(2891),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01081",cytosol,Day),
  catalyst(2891,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(2892),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00068",cytosol,Day),
  catalyst(2892,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01081",cytosol,Day) :-
  not exclude(2892),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00068",cytosol,Day),
  catalyst(2892,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2910),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C04294",cytosol,Day),
  catalyst(2910,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04327",cytosol,Day) :-
  not exclude(2910),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C04294",cytosol,Day),
  catalyst(2910,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(2920),
  Day >= 1,
  in_compartment(Experiment,"C00082",cytosol,Day),
  in_compartment(Experiment,"C00097",cytosol,Day),
  in_compartment(Experiment,"DTP",cytosol,Day),
  catalyst(2920,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04294",cytosol,Day) :-
  not exclude(2920),
  Day >= 1,
  in_compartment(Experiment,"C00082",cytosol,Day),
  in_compartment(Experiment,"C00097",cytosol,Day),
  in_compartment(Experiment,"DTP",cytosol,Day),
  catalyst(2920,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"HBA",cytosol,Day) :-
  not exclude(2920),
  Day >= 1,
  in_compartment(Experiment,"C00082",cytosol,Day),
  in_compartment(Experiment,"C00097",cytosol,Day),
  in_compartment(Experiment,"DTP",cytosol,Day),
  catalyst(2920,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2940),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C04556",cytosol,Day),
  catalyst(2940,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04752",cytosol,Day) :-
  not exclude(2940),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C04556",cytosol,Day),
  catalyst(2940,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(2950),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01279",cytosol,Day),
  catalyst(2950,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04556",cytosol,Day) :-
  not exclude(2950),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01279",cytosol,Day),
  catalyst(2950,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01279",cytosol,Day) :-
  not exclude(2960),
  Day >= 1,
  in_compartment(Experiment,"C03373",cytosol,Day),
  catalyst(2960,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(2970),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00068",cytosol,Day),
  catalyst(2970,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03028",cytosol,Day) :-
  not exclude(2970),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00068",cytosol,Day),
  catalyst(2970,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(2980),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00378",cytosol,Day),
  catalyst(2980,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00068",cytosol,Day) :-
  not exclude(2980),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00378",cytosol,Day),
  catalyst(2980,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(2990),
  Day >= 1,
  in_compartment(Experiment,"C00165",cytosol,Day),
  in_compartment(Experiment,"C01203",cytosol,Day),
  in_compartment(Experiment,"C04088",cytosol,Day),
  in_compartment(Experiment,"C05223",cytosol,Day),
  in_compartment(Experiment,"C05755",cytosol,Day),
  in_compartment(Experiment,"C05764",cytosol,Day),
  in_compartment(Experiment,"C06253",cytosol,Day),
  in_compartment(Experiment,"C161ACP",cytosol,Day),
  in_compartment(Experiment,"C182ACP",cytosol,Day),
  catalyst(2990,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00422",cytosol,Day) :-
  not exclude(2990),
  Day >= 1,
  in_compartment(Experiment,"C00165",cytosol,Day),
  in_compartment(Experiment,"C01203",cytosol,Day),
  in_compartment(Experiment,"C04088",cytosol,Day),
  in_compartment(Experiment,"C05223",cytosol,Day),
  in_compartment(Experiment,"C05755",cytosol,Day),
  in_compartment(Experiment,"C05764",cytosol,Day),
  in_compartment(Experiment,"C06253",cytosol,Day),
  in_compartment(Experiment,"C161ACP",cytosol,Day),
  in_compartment(Experiment,"C182ACP",cytosol,Day),
  catalyst(2990,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00111",cytosol,Day) :-
  not exclude(3000),
  Day >= 1,
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C00093",cytosol,Day),
  catalyst(3000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01352",mitochondrion,Day) :-
  not exclude(3000),
  Day >= 1,
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C00093",cytosol,Day),
  catalyst(3000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(3010),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00116",cytosol,Day),
  catalyst(3010,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00093",cytosol,Day) :-
  not exclude(3010),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00116",cytosol,Day),
  catalyst(3010,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(3020),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00111",cytosol,Day),
  catalyst(3020,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00093",cytosol,Day) :-
  not exclude(3020),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00111",cytosol,Day),
  catalyst(3020,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(3030),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00184",cytosol,Day),
  catalyst(3030,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00111",cytosol,Day) :-
  not exclude(3030),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00184",cytosol,Day),
  catalyst(3030,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00033",cytosol,Day) :-
  not exclude(3040),
  Day >= 1,
  in_compartment(Experiment,"C00461",cytosol,Day),
  catalyst(3040,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00734",cytosol,Day) :-
  not exclude(3040),
  Day >= 1,
  in_compartment(Experiment,"C00461",cytosol,Day),
  catalyst(3040,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(3050),
  Day >= 1,
  in_compartment(Experiment,"C00093",cytosol,Day),
  catalyst(3050,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00116",cytosol,Day) :-
  not exclude(3050),
  Day >= 1,
  in_compartment(Experiment,"C00093",cytosol,Day),
  catalyst(3050,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00110",cytosol,Day) :-
  not exclude(3070),
  Day >= 1,
  in_compartment(Experiment,"C04252",cytosol,Day),
  catalyst(3070,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00464",cytosol,Day) :-
  not exclude(3070),
  Day >= 1,
  in_compartment(Experiment,"C04252",cytosol,Day),
  catalyst(3070,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00110",cytosol,Day) :-
  not exclude(3090),
  Day >= 1,
  in_compartment(Experiment,"C00063",cytosol,Day),
  in_compartment(Experiment,"C00381",cytosol,Day),
  catalyst(3090,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00112",cytosol,Day) :-
  not exclude(3090),
  Day >= 1,
  in_compartment(Experiment,"C00063",cytosol,Day),
  in_compartment(Experiment,"C00381",cytosol,Day),
  catalyst(3090,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01419",cytosol,Day) :-
  not exclude(3120),
  Day >= 1,
  in_compartment(Experiment,"C00041",cytosol,Day),
  in_compartment(Experiment,"C00051",cytosol,Day),
  catalyst(3120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05729",cytosol,Day) :-
  not exclude(3120),
  Day >= 1,
  in_compartment(Experiment,"C00041",cytosol,Day),
  in_compartment(Experiment,"C00051",cytosol,Day),
  catalyst(3120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(3130),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00127",cytosol,Day),
  catalyst(3130,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00051",cytosol,Day) :-
  not exclude(3130),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00127",cytosol,Day),
  catalyst(3130,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00127",cytosol,Day) :-
  not exclude(3141),
  Day >= 1,
  in_compartment(Experiment,"C00027",cytosol,Day),
  in_compartment(Experiment,"C00051",cytosol,Day),
  catalyst(3141,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00027",cytosol,Day) :-
  not exclude(3142),
  Day >= 1,
  in_compartment(Experiment,"C00127",cytosol,Day),
  catalyst(3142,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00051",cytosol,Day) :-
  not exclude(3142),
  Day >= 1,
  in_compartment(Experiment,"C00127",cytosol,Day),
  catalyst(3142,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(3160),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00097",cytosol,Day),
  catalyst(3160,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(3160),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00097",cytosol,Day),
  catalyst(3160,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00669",cytosol,Day) :-
  not exclude(3160),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00097",cytosol,Day),
  catalyst(3160,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(3180),
  Day >= 1,
  in_compartment(Experiment,"C02038",cytosol,Day),
  in_compartment(Experiment,"C02593",cytosol,Day),
  catalyst(3180,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03881",cytosol,Day) :-
  not exclude(3180),
  Day >= 1,
  in_compartment(Experiment,"C02038",cytosol,Day),
  in_compartment(Experiment,"C02593",cytosol,Day),
  catalyst(3180,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",mitochondrion,Day) :-
  not exclude(3211),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00424",mitochondrion,Day),
  catalyst(3211,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00186",mitochondrion,Day) :-
  not exclude(3211),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00424",mitochondrion,Day),
  catalyst(3211,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",mitochondrion,Day) :-
  not exclude(3212),
  Day >= 1,
  in_compartment(Experiment,"C00004",mitochondrion,Day),
  in_compartment(Experiment,"C00186",mitochondrion,Day),
  catalyst(3212,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00424",mitochondrion,Day) :-
  not exclude(3212),
  Day >= 1,
  in_compartment(Experiment,"C00004",mitochondrion,Day),
  in_compartment(Experiment,"C00186",mitochondrion,Day),
  catalyst(3212,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",mitochondrion,Day) :-
  not exclude(3220),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00555",mitochondrion,Day),
  catalyst(3220,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00334",mitochondrion,Day) :-
  not exclude(3220),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00555",mitochondrion,Day),
  catalyst(3220,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",mitochondrion,Day) :-
  not exclude(3230),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00148",mitochondrion,Day),
  catalyst(3230,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03912",mitochondrion,Day) :-
  not exclude(3230),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00148",mitochondrion,Day),
  catalyst(3230,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03912",cytosol,Day) :-
  not exclude(3281),
  Day >= 1,
  in_compartment(Experiment,"C01165",cytosol,Day),
  catalyst(3281,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01165",cytosol,Day) :-
  not exclude(3282),
  Day >= 1,
  in_compartment(Experiment,"C03912",cytosol,Day),
  catalyst(3282,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(3290),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C03734",cytosol,Day),
  catalyst(3290,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(3290),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C03734",cytosol,Day),
  catalyst(3290,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01165",cytosol,Day) :-
  not exclude(3290),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C03734",cytosol,Day),
  catalyst(3290,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(3300),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C03734",cytosol,Day),
  catalyst(3300,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(3300),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C03734",cytosol,Day),
  catalyst(3300,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01165",cytosol,Day) :-
  not exclude(3300),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C03734",cytosol,Day),
  catalyst(3300,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(3310),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(3310,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03734",cytosol,Day) :-
  not exclude(3310),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(3310,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00027",cytosol,Day) :-
  not exclude(3320),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C02567",cytosol,Day),
  catalyst(3320,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00612",cytosol,Day) :-
  not exclude(3320),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C02567",cytosol,Day),
  catalyst(3320,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02229",cytosol,Day) :-
  not exclude(3320),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C02567",cytosol,Day),
  catalyst(3320,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(3330),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00750",cytosol,Day),
  catalyst(3330,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02567",cytosol,Day) :-
  not exclude(3330),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00750",cytosol,Day),
  catalyst(3330,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00027",cytosol,Day) :-
  not exclude(3350),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00612",cytosol,Day),
  catalyst(3350,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02229",cytosol,Day) :-
  not exclude(3350),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00612",cytosol,Day),
  catalyst(3350,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02714",cytosol,Day) :-
  not exclude(3350),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00612",cytosol,Day),
  catalyst(3350,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(3370),
  Day >= 1,
  in_compartment(Experiment,"C02693",cytosol,Day),
  catalyst(3370,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00954",cytosol,Day) :-
  not exclude(3370),
  Day >= 1,
  in_compartment(Experiment,"C02693",cytosol,Day),
  catalyst(3370,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",mitochondrion,Day) :-
  not exclude(3390),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00066",mitochondrion,Day),
  in_compartment(Experiment,"C00078",mitochondrion,Day),
  catalyst(3390,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",mitochondrion,Day) :-
  not exclude(3390),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00066",mitochondrion,Day),
  in_compartment(Experiment,"C00078",mitochondrion,Day),
  catalyst(3390,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03512",mitochondrion,Day) :-
  not exclude(3390),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00066",mitochondrion,Day),
  in_compartment(Experiment,"C00078",mitochondrion,Day),
  catalyst(3390,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"MACAC",cytosol,Day) :-
  not exclude(3420),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00544",cytosol,Day),
  catalyst(3420,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(3430),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C01179",cytosol,Day),
  catalyst(3430,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00544",cytosol,Day) :-
  not exclude(3430),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C01179",cytosol,Day),
  catalyst(3430,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(3440),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C02220",cytosol,Day),
  catalyst(3440,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(3440),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C02220",cytosol,Day),
  catalyst(3440,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00322",cytosol,Day) :-
  not exclude(3440),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C02220",cytosol,Day),
  catalyst(3440,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(3450),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C03824",cytosol,Day),
  catalyst(3450,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02220",cytosol,Day) :-
  not exclude(3450),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C03824",cytosol,Day),
  catalyst(3450,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00041",cytosol,Day) :-
  not exclude(3480),
  Day >= 1,
  in_compartment(Experiment,"C02794",cytosol,Day),
  catalyst(3480,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00632",cytosol,Day) :-
  not exclude(3480),
  Day >= 1,
  in_compartment(Experiment,"C02794",cytosol,Day),
  catalyst(3480,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(3490),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00328",cytosol,Day),
  catalyst(3490,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02794",cytosol,Day) :-
  not exclude(3490),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00328",cytosol,Day),
  catalyst(3490,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00041",cytosol,Day) :-
  not exclude(3500),
  Day >= 1,
  in_compartment(Experiment,"C00328",cytosol,Day),
  catalyst(3500,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00108",cytosol,Day) :-
  not exclude(3500),
  Day >= 1,
  in_compartment(Experiment,"C00328",cytosol,Day),
  catalyst(3500,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00058",cytosol,Day) :-
  not exclude(3510),
  Day >= 1,
  in_compartment(Experiment,"C02700",cytosol,Day),
  catalyst(3510,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00328",cytosol,Day) :-
  not exclude(3510),
  Day >= 1,
  in_compartment(Experiment,"C02700",cytosol,Day),
  catalyst(3510,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02700",cytosol,Day) :-
  not exclude(3520),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00078",cytosol,Day),
  catalyst(3520,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",mitochondrion,Day) :-
  not exclude(3540),
  Day >= 1,
  in_compartment(Experiment,"C00006",mitochondrion,Day),
  in_compartment(Experiment,"C00084",mitochondrion,Day),
  catalyst(3540,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00033",mitochondrion,Day) :-
  not exclude(3540),
  Day >= 1,
  in_compartment(Experiment,"C00006",mitochondrion,Day),
  in_compartment(Experiment,"C00084",mitochondrion,Day),
  catalyst(3540,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",mitochondrion,Day) :-
  not exclude(3550),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00084",mitochondrion,Day),
  catalyst(3550,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00033",mitochondrion,Day) :-
  not exclude(3550),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00084",mitochondrion,Day),
  catalyst(3550,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(3571),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C01179",cytosol,Day),
  catalyst(3571,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00082",cytosol,Day) :-
  not exclude(3571),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C01179",cytosol,Day),
  catalyst(3571,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(3572),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00082",cytosol,Day),
  catalyst(3572,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01179",cytosol,Day) :-
  not exclude(3572),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00082",cytosol,Day),
  catalyst(3572,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00078",cytosol,Day) :-
  not exclude(3590),
  Day >= 1,
  in_compartment(Experiment,"C00065",cytosol,Day),
  in_compartment(Experiment,"C03506",cytosol,Day),
  catalyst(3590,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00118",cytosol,Day) :-
  not exclude(3590),
  Day >= 1,
  in_compartment(Experiment,"C00065",cytosol,Day),
  in_compartment(Experiment,"C03506",cytosol,Day),
  catalyst(3590,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(3600),
  Day >= 1,
  in_compartment(Experiment,"C01302",cytosol,Day),
  catalyst(3600,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03506",cytosol,Day) :-
  not exclude(3600),
  Day >= 1,
  in_compartment(Experiment,"C01302",cytosol,Day),
  catalyst(3600,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01302",cytosol,Day) :-
  not exclude(3610),
  Day >= 1,
  in_compartment(Experiment,"C04302",cytosol,Day),
  catalyst(3610,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(3620),
  Day >= 1,
  in_compartment(Experiment,"C00108",cytosol,Day),
  in_compartment(Experiment,"C00119",cytosol,Day),
  catalyst(3620,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04302",cytosol,Day) :-
  not exclude(3620),
  Day >= 1,
  in_compartment(Experiment,"C00108",cytosol,Day),
  in_compartment(Experiment,"C00119",cytosol,Day),
  catalyst(3620,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(3630),
  Day >= 1,
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00251",cytosol,Day),
  catalyst(3630,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(3630),
  Day >= 1,
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00251",cytosol,Day),
  catalyst(3630,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00108",cytosol,Day) :-
  not exclude(3630),
  Day >= 1,
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00251",cytosol,Day),
  catalyst(3630,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(3650),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C01179",cytosol,Day),
  catalyst(3650,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00082",cytosol,Day) :-
  not exclude(3650),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C01179",cytosol,Day),
  catalyst(3650,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(3660),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00254",cytosol,Day),
  catalyst(3660,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(3660),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00254",cytosol,Day),
  catalyst(3660,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01179",cytosol,Day) :-
  not exclude(3660),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00254",cytosol,Day),
  catalyst(3660,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(3671),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00166",cytosol,Day),
  catalyst(3671,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00079",cytosol,Day) :-
  not exclude(3671),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00166",cytosol,Day),
  catalyst(3671,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(3672),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00079",cytosol,Day),
  catalyst(3672,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00166",cytosol,Day) :-
  not exclude(3672),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00079",cytosol,Day),
  catalyst(3672,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(3680),
  Day >= 1,
  in_compartment(Experiment,"C00254",cytosol,Day),
  catalyst(3680,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00166",cytosol,Day) :-
  not exclude(3680),
  Day >= 1,
  in_compartment(Experiment,"C00254",cytosol,Day),
  catalyst(3680,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00254",cytosol,Day) :-
  not exclude(3690),
  Day >= 1,
  in_compartment(Experiment,"C00251",cytosol,Day),
  catalyst(3690,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(3700),
  Day >= 1,
  in_compartment(Experiment,"C01269",cytosol,Day),
  catalyst(3700,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00251",cytosol,Day) :-
  not exclude(3700),
  Day >= 1,
  in_compartment(Experiment,"C01269",cytosol,Day),
  catalyst(3700,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(3710),
  Day >= 1,
  in_compartment(Experiment,"C00074",cytosol,Day),
  in_compartment(Experiment,"C03175",cytosol,Day),
  catalyst(3710,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01269",cytosol,Day) :-
  not exclude(3710),
  Day >= 1,
  in_compartment(Experiment,"C00074",cytosol,Day),
  in_compartment(Experiment,"C03175",cytosol,Day),
  catalyst(3710,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(3720),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00493",cytosol,Day),
  catalyst(3720,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03175",cytosol,Day) :-
  not exclude(3720),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00493",cytosol,Day),
  catalyst(3720,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(3730),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C02637",cytosol,Day),
  catalyst(3730,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00493",cytosol,Day) :-
  not exclude(3730),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C02637",cytosol,Day),
  catalyst(3730,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02637",cytosol,Day) :-
  not exclude(3740),
  Day >= 1,
  in_compartment(Experiment,"C00944",cytosol,Day),
  catalyst(3740,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(3750),
  Day >= 1,
  in_compartment(Experiment,"C04691",cytosol,Day),
  catalyst(3750,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00944",cytosol,Day) :-
  not exclude(3750),
  Day >= 1,
  in_compartment(Experiment,"C04691",cytosol,Day),
  catalyst(3750,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(3760),
  Day >= 1,
  in_compartment(Experiment,"C00074",cytosol,Day),
  in_compartment(Experiment,"C00279",cytosol,Day),
  catalyst(3760,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04691",cytosol,Day) :-
  not exclude(3760),
  Day >= 1,
  in_compartment(Experiment,"C00074",cytosol,Day),
  in_compartment(Experiment,"C00279",cytosol,Day),
  catalyst(3760,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",cytosol,Day) :-
  not exclude(3770),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C00135",cytosol,Day),
  catalyst(3770,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01152",cytosol,Day) :-
  not exclude(3770),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C00135",cytosol,Day),
  catalyst(3770,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(3780),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00135",cytosol,Day),
  in_compartment(Experiment,"C01643",cytosol,Day),
  catalyst(3780,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(3780),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00135",cytosol,Day),
  in_compartment(Experiment,"C01643",cytosol,Day),
  catalyst(3780,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02988",cytosol,Day) :-
  not exclude(3780),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00135",cytosol,Day),
  in_compartment(Experiment,"C01643",cytosol,Day),
  catalyst(3780,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(3800),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00860",cytosol,Day),
  catalyst(3800,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00135",cytosol,Day) :-
  not exclude(3800),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00860",cytosol,Day),
  catalyst(3800,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(3810),
  Day >= 1,
  in_compartment(Experiment,"C01100",cytosol,Day),
  catalyst(3810,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00860",cytosol,Day) :-
  not exclude(3810),
  Day >= 1,
  in_compartment(Experiment,"C01100",cytosol,Day),
  catalyst(3810,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04896",cytosol,Day) :-
  not exclude(3850),
  Day >= 1,
  in_compartment(Experiment,"C03883",cytosol,Day),
  catalyst(3850,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(3860),
  Day >= 1,
  in_compartment(Experiment,"C02739",cytosol,Day),
  catalyst(3860,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03883",cytosol,Day) :-
  not exclude(3860),
  Day >= 1,
  in_compartment(Experiment,"C02739",cytosol,Day),
  catalyst(3860,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00390",mitochondrion,Day) :-
  not exclude(3880),
  Day >= 1,
  in_compartment(Experiment,"C00315",cytosol,Day),
  in_compartment(Experiment,"C01967",mitochondrion,Day),
  catalyst(3880,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00986",cytosol,Day) :-
  not exclude(3880),
  Day >= 1,
  in_compartment(Experiment,"C00315",cytosol,Day),
  in_compartment(Experiment,"C01967",mitochondrion,Day),
  catalyst(3880,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(3890),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00062",cytosol,Day),
  in_compartment(Experiment,"C01636",cytosol,Day),
  catalyst(3890,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(3890),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00062",cytosol,Day),
  in_compartment(Experiment,"C01636",cytosol,Day),
  catalyst(3890,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02163",cytosol,Day) :-
  not exclude(3890),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00062",cytosol,Day),
  in_compartment(Experiment,"C01636",cytosol,Day),
  catalyst(3890,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00077",cytosol,Day) :-
  not exclude(3900),
  Day >= 1,
  in_compartment(Experiment,"C00062",cytosol,Day),
  catalyst(3900,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00086",cytosol,Day) :-
  not exclude(3900),
  Day >= 1,
  in_compartment(Experiment,"C00062",cytosol,Day),
  catalyst(3900,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00170",cytosol,Day) :-
  not exclude(3930),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C00134",cytosol,Day),
  catalyst(3930,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00315",cytosol,Day) :-
  not exclude(3930),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C00134",cytosol,Day),
  catalyst(3930,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(3941),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  catalyst(3941,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01137",cytosol,Day) :-
  not exclude(3941),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  catalyst(3941,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00019",cytosol,Day) :-
  not exclude(3942),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C01137",cytosol,Day),
  catalyst(3942,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(3950),
  Day >= 1,
  in_compartment(Experiment,"C00077",cytosol,Day),
  catalyst(3950,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00134",cytosol,Day) :-
  not exclude(3950),
  Day >= 1,
  in_compartment(Experiment,"C00077",cytosol,Day),
  catalyst(3950,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00062",cytosol,Day) :-
  not exclude(3961),
  Day >= 1,
  in_compartment(Experiment,"C03406",cytosol,Day),
  catalyst(3961,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00122",cytosol,Day) :-
  not exclude(3961),
  Day >= 1,
  in_compartment(Experiment,"C03406",cytosol,Day),
  catalyst(3961,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03406",cytosol,Day) :-
  not exclude(3962),
  Day >= 1,
  in_compartment(Experiment,"C00062",cytosol,Day),
  in_compartment(Experiment,"C00122",cytosol,Day),
  catalyst(3962,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(3971),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C00327",cytosol,Day),
  catalyst(3971,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(3971),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C00327",cytosol,Day),
  catalyst(3971,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03406",cytosol,Day) :-
  not exclude(3971),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C00327",cytosol,Day),
  catalyst(3971,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(3972),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03406",cytosol,Day),
  catalyst(3972,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00049",cytosol,Day) :-
  not exclude(3972),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03406",cytosol,Day),
  catalyst(3972,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00327",cytosol,Day) :-
  not exclude(3972),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03406",cytosol,Day),
  catalyst(3972,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(3980),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00077",cytosol,Day),
  catalyst(3980,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01165",cytosol,Day) :-
  not exclude(3980),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00077",cytosol,Day),
  catalyst(3980,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(3990),
  Day >= 1,
  in_compartment(Experiment,"C00077",cytosol,Day),
  in_compartment(Experiment,"C00169",cytosol,Day),
  catalyst(3990,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00327",cytosol,Day) :-
  not exclude(3990),
  Day >= 1,
  in_compartment(Experiment,"C00077",cytosol,Day),
  in_compartment(Experiment,"C00169",cytosol,Day),
  catalyst(3990,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(4000),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  catalyst(4000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(4000),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  catalyst(4000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(4000),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  catalyst(4000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00169",cytosol,Day) :-
  not exclude(4000),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  catalyst(4000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",mitochondrion,Day) :-
  not exclude(4020),
  Day >= 1,
  in_compartment(Experiment,"C00025",mitochondrion,Day),
  in_compartment(Experiment,"C01250",mitochondrion,Day),
  catalyst(4020,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00437",mitochondrion,Day) :-
  not exclude(4020),
  Day >= 1,
  in_compartment(Experiment,"C00025",mitochondrion,Day),
  in_compartment(Experiment,"C01250",mitochondrion,Day),
  catalyst(4020,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",mitochondrion,Day) :-
  not exclude(4030),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C04133",mitochondrion,Day),
  catalyst(4030,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",mitochondrion,Day) :-
  not exclude(4030),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C04133",mitochondrion,Day),
  catalyst(4030,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01250",mitochondrion,Day) :-
  not exclude(4030),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C04133",mitochondrion,Day),
  catalyst(4030,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",mitochondrion,Day) :-
  not exclude(4050),
  Day >= 1,
  in_compartment(Experiment,"C00024",mitochondrion,Day),
  in_compartment(Experiment,"C00025",mitochondrion,Day),
  catalyst(4050,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00624",mitochondrion,Day) :-
  not exclude(4050),
  Day >= 1,
  in_compartment(Experiment,"C00024",mitochondrion,Day),
  in_compartment(Experiment,"C00025",mitochondrion,Day),
  catalyst(4050,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",mitochondrion,Day) :-
  not exclude(4060),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00047",mitochondrion,Day),
  in_compartment(Experiment,"C01646",mitochondrion,Day),
  catalyst(4060,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",mitochondrion,Day) :-
  not exclude(4060),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00047",mitochondrion,Day),
  in_compartment(Experiment,"C01646",mitochondrion,Day),
  catalyst(4060,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01931",mitochondrion,Day) :-
  not exclude(4060),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00047",mitochondrion,Day),
  in_compartment(Experiment,"C01646",mitochondrion,Day),
  catalyst(4060,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(4070),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00047",cytosol,Day),
  in_compartment(Experiment,"C01646",cytosol,Day),
  catalyst(4070,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(4070),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00047",cytosol,Day),
  in_compartment(Experiment,"C01646",cytosol,Day),
  catalyst(4070,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01931",cytosol,Day) :-
  not exclude(4070),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00047",cytosol,Day),
  in_compartment(Experiment,"C01646",cytosol,Day),
  catalyst(4070,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(4100),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00956",cytosol,Day),
  catalyst(4100,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(4100),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00956",cytosol,Day),
  catalyst(4100,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(4100),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00956",cytosol,Day),
  catalyst(4100,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04076",cytosol,Day) :-
  not exclude(4100),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00956",cytosol,Day),
  catalyst(4100,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(4121),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00322",cytosol,Day),
  catalyst(4121,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00956",cytosol,Day) :-
  not exclude(4121),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00322",cytosol,Day),
  catalyst(4121,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(4122),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00956",cytosol,Day),
  catalyst(4122,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00322",cytosol,Day) :-
  not exclude(4122),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00956",cytosol,Day),
  catalyst(4122,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(4131),
  Day >= 1,
  in_compartment(Experiment,"C05533",mitochondrion,Day),
  catalyst(4131,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00322",mitochondrion,Day) :-
  not exclude(4131),
  Day >= 1,
  in_compartment(Experiment,"C05533",mitochondrion,Day),
  catalyst(4131,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05533",mitochondrion,Day) :-
  not exclude(4132),
  Day >= 1,
  in_compartment(Experiment,"C00011",mitochondrion,Day),
  in_compartment(Experiment,"C00322",mitochondrion,Day),
  catalyst(4132,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(4170),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C02504",cytosol,Day),
  catalyst(4170,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(4170),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C02504",cytosol,Day),
  catalyst(4170,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04236",cytosol,Day) :-
  not exclude(4170),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C02504",cytosol,Day),
  catalyst(4170,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02504",cytosol,Day) :-
  not exclude(4191),
  Day >= 1,
  in_compartment(Experiment,"C04411",cytosol,Day),
  catalyst(4191,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04411",cytosol,Day) :-
  not exclude(4192),
  Day >= 1,
  in_compartment(Experiment,"C02504",cytosol,Day),
  catalyst(4192,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(4250),
  Day >= 1,
  in_compartment(Experiment,"C00022",mitochondrion,Day),
  catalyst(4250,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00900",mitochondrion,Day) :-
  not exclude(4250),
  Day >= 1,
  in_compartment(Experiment,"C00022",mitochondrion,Day),
  catalyst(4250,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"ABUT",mitochondrion,Day) :-
  not exclude(4260),
  Day >= 1,
  in_compartment(Experiment,"C00022",mitochondrion,Day),
  in_compartment(Experiment,"C00109",mitochondrion,Day),
  catalyst(4260,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(4260),
  Day >= 1,
  in_compartment(Experiment,"C00022",mitochondrion,Day),
  in_compartment(Experiment,"C00109",mitochondrion,Day),
  catalyst(4260,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(4271),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C04236",cytosol,Day),
  catalyst(4271,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00123",cytosol,Day) :-
  not exclude(4271),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C04236",cytosol,Day),
  catalyst(4271,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(4272),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00123",cytosol,Day),
  catalyst(4272,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04236",cytosol,Day) :-
  not exclude(4272),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00123",cytosol,Day),
  catalyst(4272,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(4281),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"OIVAL",cytosol,Day),
  catalyst(4281,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00183",cytosol,Day) :-
  not exclude(4281),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"OIVAL",cytosol,Day),
  catalyst(4281,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(4282),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00183",cytosol,Day),
  catalyst(4282,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"OIVAL",cytosol,Day) :-
  not exclude(4282),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00183",cytosol,Day),
  catalyst(4282,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(4291),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00141",cytosol,Day),
  catalyst(4291,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00407",cytosol,Day) :-
  not exclude(4291),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00141",cytosol,Day),
  catalyst(4291,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(4292),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00407",cytosol,Day),
  catalyst(4292,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00141",cytosol,Day) :-
  not exclude(4292),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00407",cytosol,Day),
  catalyst(4292,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",mitochondrion,Day) :-
  not exclude(4301),
  Day >= 1,
  in_compartment(Experiment,"C00025",mitochondrion,Day),
  in_compartment(Experiment,"C00141",mitochondrion,Day),
  catalyst(4301,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00407",mitochondrion,Day) :-
  not exclude(4301),
  Day >= 1,
  in_compartment(Experiment,"C00025",mitochondrion,Day),
  in_compartment(Experiment,"C00141",mitochondrion,Day),
  catalyst(4301,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",mitochondrion,Day) :-
  not exclude(4302),
  Day >= 1,
  in_compartment(Experiment,"C00026",mitochondrion,Day),
  in_compartment(Experiment,"C00407",mitochondrion,Day),
  catalyst(4302,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00141",mitochondrion,Day) :-
  not exclude(4302),
  Day >= 1,
  in_compartment(Experiment,"C00026",mitochondrion,Day),
  in_compartment(Experiment,"C00407",mitochondrion,Day),
  catalyst(4302,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",mitochondrion,Day) :-
  not exclude(4311),
  Day >= 1,
  in_compartment(Experiment,"C00025",mitochondrion,Day),
  in_compartment(Experiment,"C04236",mitochondrion,Day),
  catalyst(4311,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00123",mitochondrion,Day) :-
  not exclude(4311),
  Day >= 1,
  in_compartment(Experiment,"C00025",mitochondrion,Day),
  in_compartment(Experiment,"C04236",mitochondrion,Day),
  catalyst(4311,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",mitochondrion,Day) :-
  not exclude(4312),
  Day >= 1,
  in_compartment(Experiment,"C00026",mitochondrion,Day),
  in_compartment(Experiment,"C00123",mitochondrion,Day),
  catalyst(4312,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04236",mitochondrion,Day) :-
  not exclude(4312),
  Day >= 1,
  in_compartment(Experiment,"C00026",mitochondrion,Day),
  in_compartment(Experiment,"C00123",mitochondrion,Day),
  catalyst(4312,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00054",cytosol,Day) :-
  not exclude(4330),
  Day >= 1,
  in_compartment(Experiment,"C00053",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(4330,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00094",cytosol,Day) :-
  not exclude(4330),
  Day >= 1,
  in_compartment(Experiment,"C00053",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(4330,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00343",cytosol,Day) :-
  not exclude(4330),
  Day >= 1,
  in_compartment(Experiment,"C00053",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(4330,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(4340),
  Day >= 1,
  in_compartment(Experiment,"C00054",cytosol,Day),
  catalyst(4340,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(4340),
  Day >= 1,
  in_compartment(Experiment,"C00054",cytosol,Day),
  catalyst(4340,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00033",cytosol,Day) :-
  not exclude(4350),
  Day >= 1,
  in_compartment(Experiment,"C00283",cytosol,Day),
  in_compartment(Experiment,"C00979",cytosol,Day),
  catalyst(4350,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00097",cytosol,Day) :-
  not exclude(4350),
  Day >= 1,
  in_compartment(Experiment,"C00283",cytosol,Day),
  in_compartment(Experiment,"C00979",cytosol,Day),
  catalyst(4350,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(4360),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00065",cytosol,Day),
  catalyst(4360,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00979",cytosol,Day) :-
  not exclude(4360),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00065",cytosol,Day),
  catalyst(4360,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(4371),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00094",cytosol,Day),
  catalyst(4371,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00283",cytosol,Day) :-
  not exclude(4371),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00094",cytosol,Day),
  catalyst(4371,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(4372),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00283",cytosol,Day),
  catalyst(4372,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00094",cytosol,Day) :-
  not exclude(4372),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00283",cytosol,Day),
  catalyst(4372,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(4380),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00224",cytosol,Day),
  catalyst(4380,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00053",cytosol,Day) :-
  not exclude(4380),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00224",cytosol,Day),
  catalyst(4380,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(4390),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00059",cytosol,Day),
  catalyst(4390,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00224",cytosol,Day) :-
  not exclude(4390),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00059",cytosol,Day),
  catalyst(4390,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",cytosol,Day) :-
  not exclude(4400),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C04441",cytosol,Day),
  catalyst(4400,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04692",cytosol,Day) :-
  not exclude(4400),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C04441",cytosol,Day),
  catalyst(4400,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(4410),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00073",cytosol,Day),
  catalyst(4410,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(4410),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00073",cytosol,Day),
  catalyst(4410,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00019",cytosol,Day) :-
  not exclude(4410),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00073",cytosol,Day),
  catalyst(4410,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(4421),
  Day >= 1,
  in_compartment(Experiment,"C01118",cytosol,Day),
  catalyst(4421,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",cytosol,Day) :-
  not exclude(4421),
  Day >= 1,
  in_compartment(Experiment,"C01118",cytosol,Day),
  catalyst(4421,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00109",cytosol,Day) :-
  not exclude(4421),
  Day >= 1,
  in_compartment(Experiment,"C01118",cytosol,Day),
  catalyst(4421,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01118",cytosol,Day) :-
  not exclude(4422),
  Day >= 1,
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C00109",cytosol,Day),
  catalyst(4422,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00033",cytosol,Day) :-
  not exclude(4430),
  Day >= 1,
  in_compartment(Experiment,"C00283",cytosol,Day),
  in_compartment(Experiment,"C01077",cytosol,Day),
  catalyst(4430,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05330",cytosol,Day) :-
  not exclude(4430),
  Day >= 1,
  in_compartment(Experiment,"C00283",cytosol,Day),
  in_compartment(Experiment,"C01077",cytosol,Day),
  catalyst(4430,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(4451),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00263",cytosol,Day),
  catalyst(4451,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01077",cytosol,Day) :-
  not exclude(4451),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00263",cytosol,Day),
  catalyst(4451,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00024",cytosol,Day) :-
  not exclude(4452),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C01077",cytosol,Day),
  catalyst(4452,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00263",cytosol,Day) :-
  not exclude(4452),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C01077",cytosol,Day),
  catalyst(4452,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00073",cytosol,Day) :-
  not exclude(4470),
  Day >= 1,
  in_compartment(Experiment,"C00440",cytosol,Day),
  in_compartment(Experiment,"C05330",cytosol,Day),
  catalyst(4470,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00101",cytosol,Day) :-
  not exclude(4470),
  Day >= 1,
  in_compartment(Experiment,"C00440",cytosol,Day),
  in_compartment(Experiment,"C05330",cytosol,Day),
  catalyst(4470,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00073",cytosol,Day) :-
  not exclude(4480),
  Day >= 1,
  in_compartment(Experiment,"C04489",cytosol,Day),
  in_compartment(Experiment,"C05330",cytosol,Day),
  catalyst(4480,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04144",cytosol,Day) :-
  not exclude(4480),
  Day >= 1,
  in_compartment(Experiment,"C04489",cytosol,Day),
  in_compartment(Experiment,"C05330",cytosol,Day),
  catalyst(4480,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00212",cytosol,Day) :-
  not exclude(4490),
  Day >= 1,
  in_compartment(Experiment,"C00021",cytosol,Day),
  catalyst(4490,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05330",cytosol,Day) :-
  not exclude(4490),
  Day >= 1,
  in_compartment(Experiment,"C00021",cytosol,Day),
  catalyst(4490,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(4500),
  Day >= 1,
  in_compartment(Experiment,"C02291",cytosol,Day),
  catalyst(4500,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(4500),
  Day >= 1,
  in_compartment(Experiment,"C02291",cytosol,Day),
  catalyst(4500,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05330",cytosol,Day) :-
  not exclude(4500),
  Day >= 1,
  in_compartment(Experiment,"C02291",cytosol,Day),
  catalyst(4500,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(4510),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00188",cytosol,Day),
  catalyst(4510,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00033",cytosol,Day) :-
  not exclude(4510),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00188",cytosol,Day),
  catalyst(4510,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00037",cytosol,Day) :-
  not exclude(4510),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00188",cytosol,Day),
  catalyst(4510,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(4520),
  Day >= 1,
  in_compartment(Experiment,"C00065",cytosol,Day),
  catalyst(4520,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(4520),
  Day >= 1,
  in_compartment(Experiment,"C00065",cytosol,Day),
  catalyst(4520,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(4540),
  Day >= 1,
  in_compartment(Experiment,"C00188",cytosol,Day),
  catalyst(4540,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00109",cytosol,Day) :-
  not exclude(4540),
  Day >= 1,
  in_compartment(Experiment,"C00188",cytosol,Day),
  catalyst(4540,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(4551),
  Day >= 1,
  in_compartment(Experiment,"C00037",mitochondrion,Day),
  in_compartment(Experiment,"C00248",mitochondrion,Day),
  catalyst(4551,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01242",mitochondrion,Day) :-
  not exclude(4551),
  Day >= 1,
  in_compartment(Experiment,"C00037",mitochondrion,Day),
  in_compartment(Experiment,"C00248",mitochondrion,Day),
  catalyst(4551,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00037",mitochondrion,Day) :-
  not exclude(4552),
  Day >= 1,
  in_compartment(Experiment,"C00011",mitochondrion,Day),
  in_compartment(Experiment,"C01242",mitochondrion,Day),
  catalyst(4552,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00248",mitochondrion,Day) :-
  not exclude(4552),
  Day >= 1,
  in_compartment(Experiment,"C00011",mitochondrion,Day),
  in_compartment(Experiment,"C01242",mitochondrion,Day),
  catalyst(4552,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00188",cytosol,Day) :-
  not exclude(4560),
  Day >= 1,
  in_compartment(Experiment,"C00037",cytosol,Day),
  in_compartment(Experiment,"C00084",cytosol,Day),
  catalyst(4560,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02291",cytosol,Day) :-
  not exclude(4570),
  Day >= 1,
  in_compartment(Experiment,"C00065",cytosol,Day),
  in_compartment(Experiment,"C05330",cytosol,Day),
  catalyst(4570,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(4580),
  Day >= 1,
  in_compartment(Experiment,"C01102",cytosol,Day),
  catalyst(4580,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00188",cytosol,Day) :-
  not exclude(4580),
  Day >= 1,
  in_compartment(Experiment,"C01102",cytosol,Day),
  catalyst(4580,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(4590),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00263",cytosol,Day),
  catalyst(4590,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01102",cytosol,Day) :-
  not exclude(4590),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00263",cytosol,Day),
  catalyst(4590,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(4600),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00441",cytosol,Day),
  catalyst(4600,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00263",cytosol,Day) :-
  not exclude(4600),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00441",cytosol,Day),
  catalyst(4600,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(4620),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C03082",cytosol,Day),
  catalyst(4620,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(4620),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C03082",cytosol,Day),
  catalyst(4620,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00441",cytosol,Day) :-
  not exclude(4620),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C03082",cytosol,Day),
  catalyst(4620,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(4630),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  catalyst(4630,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03082",cytosol,Day) :-
  not exclude(4630),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  catalyst(4630,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(4640),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00037",cytosol,Day),
  in_compartment(Experiment,"C00101",cytosol,Day),
  catalyst(4640,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(4640),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00037",cytosol,Day),
  in_compartment(Experiment,"C00101",cytosol,Day),
  catalyst(4640,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(4640),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00037",cytosol,Day),
  in_compartment(Experiment,"C00101",cytosol,Day),
  catalyst(4640,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00143",cytosol,Day) :-
  not exclude(4640),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00037",cytosol,Day),
  in_compartment(Experiment,"C00101",cytosol,Day),
  catalyst(4640,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00037",mitochondrion,Day) :-
  not exclude(4681),
  Day >= 1,
  in_compartment(Experiment,"C00065",mitochondrion,Day),
  in_compartment(Experiment,"C00101",mitochondrion,Day),
  catalyst(4681,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00143",mitochondrion,Day) :-
  not exclude(4681),
  Day >= 1,
  in_compartment(Experiment,"C00065",mitochondrion,Day),
  in_compartment(Experiment,"C00101",mitochondrion,Day),
  catalyst(4681,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00065",mitochondrion,Day) :-
  not exclude(4682),
  Day >= 1,
  in_compartment(Experiment,"C00037",mitochondrion,Day),
  in_compartment(Experiment,"C00143",mitochondrion,Day),
  catalyst(4682,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00101",mitochondrion,Day) :-
  not exclude(4682),
  Day >= 1,
  in_compartment(Experiment,"C00037",mitochondrion,Day),
  in_compartment(Experiment,"C00143",mitochondrion,Day),
  catalyst(4682,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(4690),
  Day >= 1,
  in_compartment(Experiment,"C01005",cytosol,Day),
  catalyst(4690,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00065",cytosol,Day) :-
  not exclude(4690),
  Day >= 1,
  in_compartment(Experiment,"C01005",cytosol,Day),
  catalyst(4690,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(4700),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C03232",cytosol,Day),
  catalyst(4700,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01005",cytosol,Day) :-
  not exclude(4700),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C03232",cytosol,Day),
  catalyst(4700,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(4710),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00197",cytosol,Day),
  catalyst(4710,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03232",cytosol,Day) :-
  not exclude(4710),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00197",cytosol,Day),
  catalyst(4710,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(4720),
  Day >= 1,
  in_compartment(Experiment,"C00152",cytosol,Day),
  catalyst(4720,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00049",cytosol,Day) :-
  not exclude(4720),
  Day >= 1,
  in_compartment(Experiment,"C00152",cytosol,Day),
  catalyst(4720,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(4730),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C00066",cytosol,Day),
  catalyst(4730,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(4730),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C00066",cytosol,Day),
  catalyst(4730,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03402",cytosol,Day) :-
  not exclude(4730),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C00066",cytosol,Day),
  catalyst(4730,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",cytosol,Day) :-
  not exclude(4750),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C05330",cytosol,Day),
  catalyst(4750,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00073",cytosol,Day) :-
  not exclude(4750),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C05330",cytosol,Day),
  catalyst(4750,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(4760),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  catalyst(4760,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(4760),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  catalyst(4760,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(4760),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  catalyst(4760,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00152",cytosol,Day) :-
  not exclude(4760),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  catalyst(4760,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(4781),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(4781,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00041",cytosol,Day) :-
  not exclude(4781),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(4781,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(4782),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00041",cytosol,Day),
  catalyst(4782,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(4782),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00041",cytosol,Day),
  catalyst(4782,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(4840),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00310",cytosol,Day),
  catalyst(4840,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C06814",cytosol,Day) :-
  not exclude(4840),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00310",cytosol,Day),
  catalyst(4840,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(4850),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00216",cytosol,Day),
  catalyst(4850,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00652",cytosol,Day) :-
  not exclude(4850),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00216",cytosol,Day),
  catalyst(4850,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(4870),
  Day >= 1,
  in_compartment(Experiment,"C00352",cytosol,Day),
  catalyst(4870,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05345",cytosol,Day) :-
  not exclude(4870),
  Day >= 1,
  in_compartment(Experiment,"C00352",cytosol,Day),
  catalyst(4870,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(4880),
  Day >= 1,
  in_compartment(Experiment,"C00064",cytosol,Day),
  catalyst(4880,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(4880),
  Day >= 1,
  in_compartment(Experiment,"C00064",cytosol,Day),
  catalyst(4880,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C06156",cytosol,Day) :-
  not exclude(4891),
  Day >= 1,
  in_compartment(Experiment,"C00352",cytosol,Day),
  catalyst(4891,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00352",cytosol,Day) :-
  not exclude(4892),
  Day >= 1,
  in_compartment(Experiment,"C06156",cytosol,Day),
  catalyst(4892,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(4900),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(4900,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(4900),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(4900,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00064",cytosol,Day) :-
  not exclude(4900),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(4900,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(4910),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00026",cytosol,Day),
  catalyst(4910,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(4910),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00026",cytosol,Day),
  catalyst(4910,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(4920),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(4920,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(4920),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(4920,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(4920),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(4920,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",mitochondrion,Day) :-
  not exclude(4940),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C03912",mitochondrion,Day),
  catalyst(4940,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",mitochondrion,Day) :-
  not exclude(4940),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C03912",mitochondrion,Day),
  catalyst(4940,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00015",cytosol,Day) :-
  not exclude(4960),
  Day >= 1,
  in_compartment(Experiment,"C00043",cytosol,Day),
  catalyst(4960,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00461",cytosol,Day) :-
  not exclude(4960),
  Day >= 1,
  in_compartment(Experiment,"C00043",cytosol,Day),
  catalyst(4960,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(4971),
  Day >= 1,
  in_compartment(Experiment,"C00075",cytosol,Day),
  in_compartment(Experiment,"C04256",cytosol,Day),
  catalyst(4971,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00043",cytosol,Day) :-
  not exclude(4971),
  Day >= 1,
  in_compartment(Experiment,"C00075",cytosol,Day),
  in_compartment(Experiment,"C04256",cytosol,Day),
  catalyst(4971,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00075",cytosol,Day) :-
  not exclude(4972),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00043",cytosol,Day),
  catalyst(4972,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04256",cytosol,Day) :-
  not exclude(4972),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00043",cytosol,Day),
  catalyst(4972,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00357",cytosol,Day) :-
  not exclude(4981),
  Day >= 1,
  in_compartment(Experiment,"C04256",cytosol,Day),
  catalyst(4981,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04256",cytosol,Day) :-
  not exclude(4982),
  Day >= 1,
  in_compartment(Experiment,"C00357",cytosol,Day),
  catalyst(4982,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(4991),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00352",cytosol,Day),
  catalyst(4991,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00357",cytosol,Day) :-
  not exclude(4991),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00352",cytosol,Day),
  catalyst(4991,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00024",cytosol,Day) :-
  not exclude(4992),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00357",cytosol,Day),
  catalyst(4992,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00352",cytosol,Day) :-
  not exclude(4992),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00357",cytosol,Day),
  catalyst(4992,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(5000),
  Day >= 1,
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C05345",cytosol,Day),
  catalyst(5000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00352",cytosol,Day) :-
  not exclude(5000),
  Day >= 1,
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C05345",cytosol,Day),
  catalyst(5000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(5010),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00232",cytosol,Day),
  catalyst(5010,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",cytosol,Day) :-
  not exclude(5010),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00232",cytosol,Day),
  catalyst(5010,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(5020),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00334",cytosol,Day),
  catalyst(5020,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00232",cytosol,Day) :-
  not exclude(5020),
  Day >= 1,
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00334",cytosol,Day),
  catalyst(5020,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(5030),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(5030,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00334",cytosol,Day) :-
  not exclude(5030),
  Day >= 1,
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(5030,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5050),
  Day >= 1,
  in_compartment(Experiment,"C00286",cytosol,Day),
  catalyst(5050,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00330",cytosol,Day) :-
  not exclude(5050),
  Day >= 1,
  in_compartment(Experiment,"C00286",cytosol,Day),
  catalyst(5050,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5060),
  Day >= 1,
  in_compartment(Experiment,"C00044",cytosol,Day),
  catalyst(5060,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00387",cytosol,Day) :-
  not exclude(5060),
  Day >= 1,
  in_compartment(Experiment,"C00044",cytosol,Day),
  catalyst(5060,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00343",cytosol,Day) :-
  not exclude(5080),
  Day >= 1,
  in_compartment(Experiment,"C00063",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(5080,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00458",cytosol,Day) :-
  not exclude(5080),
  Day >= 1,
  in_compartment(Experiment,"C00063",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(5080,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00286",cytosol,Day) :-
  not exclude(5090),
  Day >= 1,
  in_compartment(Experiment,"C00044",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(5090,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00343",cytosol,Day) :-
  not exclude(5090),
  Day >= 1,
  in_compartment(Experiment,"C00044",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(5090,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00131",cytosol,Day) :-
  not exclude(5100),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(5100,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00343",cytosol,Day) :-
  not exclude(5100),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(5100,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00343",cytosol,Day) :-
  not exclude(5110),
  Day >= 1,
  in_compartment(Experiment,"C00015",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(5110,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01346",cytosol,Day) :-
  not exclude(5110),
  Day >= 1,
  in_compartment(Experiment,"C00015",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(5110,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00343",cytosol,Day) :-
  not exclude(5120),
  Day >= 1,
  in_compartment(Experiment,"C00112",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(5120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00705",cytosol,Day) :-
  not exclude(5120),
  Day >= 1,
  in_compartment(Experiment,"C00112",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(5120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00206",cytosol,Day) :-
  not exclude(5140),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(5140,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00343",cytosol,Day) :-
  not exclude(5140),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(5140,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5150),
  Day >= 1,
  in_compartment(Experiment,"C00105",cytosol,Day),
  catalyst(5150,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00299",cytosol,Day) :-
  not exclude(5150),
  Day >= 1,
  in_compartment(Experiment,"C00105",cytosol,Day),
  catalyst(5150,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5160),
  Day >= 1,
  in_compartment(Experiment,"C00655",cytosol,Day),
  catalyst(5160,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01762",cytosol,Day) :-
  not exclude(5160),
  Day >= 1,
  in_compartment(Experiment,"C00655",cytosol,Day),
  catalyst(5160,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5170),
  Day >= 1,
  in_compartment(Experiment,"C00130",cytosol,Day),
  catalyst(5170,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00294",cytosol,Day) :-
  not exclude(5170),
  Day >= 1,
  in_compartment(Experiment,"C00130",cytosol,Day),
  catalyst(5170,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5190),
  Day >= 1,
  in_compartment(Experiment,"C00020",cytosol,Day),
  catalyst(5190,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00212",cytosol,Day) :-
  not exclude(5190),
  Day >= 1,
  in_compartment(Experiment,"C00020",cytosol,Day),
  catalyst(5190,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5200),
  Day >= 1,
  in_compartment(Experiment,"C00055",cytosol,Day),
  catalyst(5200,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00475",cytosol,Day) :-
  not exclude(5200),
  Day >= 1,
  in_compartment(Experiment,"C00055",cytosol,Day),
  catalyst(5200,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5210),
  Day >= 1,
  in_compartment(Experiment,"C00239",cytosol,Day),
  catalyst(5210,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00881",cytosol,Day) :-
  not exclude(5210),
  Day >= 1,
  in_compartment(Experiment,"C00239",cytosol,Day),
  catalyst(5210,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5220),
  Day >= 1,
  in_compartment(Experiment,"C00362",cytosol,Day),
  catalyst(5220,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00330",cytosol,Day) :-
  not exclude(5220),
  Day >= 1,
  in_compartment(Experiment,"C00362",cytosol,Day),
  catalyst(5220,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5230),
  Day >= 1,
  in_compartment(Experiment,"C00360",cytosol,Day),
  catalyst(5230,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00559",cytosol,Day) :-
  not exclude(5230),
  Day >= 1,
  in_compartment(Experiment,"C00360",cytosol,Day),
  catalyst(5230,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5250),
  Day >= 1,
  in_compartment(Experiment,"C00365",cytosol,Day),
  catalyst(5250,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00526",cytosol,Day) :-
  not exclude(5250),
  Day >= 1,
  in_compartment(Experiment,"C00365",cytosol,Day),
  catalyst(5250,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(5260),
  Day >= 1,
  in_compartment(Experiment,"C00458",cytosol,Day),
  catalyst(5260,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00460",cytosol,Day) :-
  not exclude(5260),
  Day >= 1,
  in_compartment(Experiment,"C00458",cytosol,Day),
  catalyst(5260,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00106",cytosol,Day) :-
  not exclude(5301),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00299",cytosol,Day),
  catalyst(5301,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00620",cytosol,Day) :-
  not exclude(5301),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00299",cytosol,Day),
  catalyst(5301,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5302),
  Day >= 1,
  in_compartment(Experiment,"C00106",cytosol,Day),
  in_compartment(Experiment,"C00620",cytosol,Day),
  catalyst(5302,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00299",cytosol,Day) :-
  not exclude(5302),
  Day >= 1,
  in_compartment(Experiment,"C00106",cytosol,Day),
  in_compartment(Experiment,"C00620",cytosol,Day),
  catalyst(5302,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(5310),
  Day >= 1,
  in_compartment(Experiment,"C00119",cytosol,Day),
  in_compartment(Experiment,"C00242",cytosol,Day),
  catalyst(5310,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00144",cytosol,Day) :-
  not exclude(5310),
  Day >= 1,
  in_compartment(Experiment,"C00119",cytosol,Day),
  in_compartment(Experiment,"C00242",cytosol,Day),
  catalyst(5310,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5330),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00387",cytosol,Day),
  catalyst(5330,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00144",cytosol,Day) :-
  not exclude(5330),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00387",cytosol,Day),
  catalyst(5330,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5340),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00294",cytosol,Day),
  catalyst(5340,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00130",cytosol,Day) :-
  not exclude(5340),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00294",cytosol,Day),
  catalyst(5340,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(5350),
  Day >= 1,
  in_compartment(Experiment,"C00147",cytosol,Day),
  catalyst(5350,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00262",cytosol,Day) :-
  not exclude(5350),
  Day >= 1,
  in_compartment(Experiment,"C00147",cytosol,Day),
  catalyst(5350,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5361),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00360",cytosol,Day),
  catalyst(5361,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00206",cytosol,Day) :-
  not exclude(5361),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00360",cytosol,Day),
  catalyst(5361,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(5362),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00206",cytosol,Day),
  catalyst(5362,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00360",cytosol,Day) :-
  not exclude(5362),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00206",cytosol,Day),
  catalyst(5362,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00081",cytosol,Day) :-
  not exclude(5371),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00104",cytosol,Day),
  catalyst(5371,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00104",cytosol,Day) :-
  not exclude(5371),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00104",cytosol,Day),
  catalyst(5371,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(5372),
  Day >= 1,
  in_compartment(Experiment,"C00081",cytosol,Day),
  in_compartment(Experiment,"C00104",cytosol,Day),
  catalyst(5372,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00104",cytosol,Day) :-
  not exclude(5372),
  Day >= 1,
  in_compartment(Experiment,"C00081",cytosol,Day),
  in_compartment(Experiment,"C00104",cytosol,Day),
  catalyst(5372,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5381),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00035",cytosol,Day),
  catalyst(5381,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00044",cytosol,Day) :-
  not exclude(5381),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00035",cytosol,Day),
  catalyst(5381,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(5382),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00044",cytosol,Day),
  catalyst(5382,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00035",cytosol,Day) :-
  not exclude(5382),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00044",cytosol,Day),
  catalyst(5382,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5391),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00206",cytosol,Day),
  catalyst(5391,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00131",cytosol,Day) :-
  not exclude(5391),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00206",cytosol,Day),
  catalyst(5391,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(5392),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00131",cytosol,Day),
  catalyst(5392,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00206",cytosol,Day) :-
  not exclude(5392),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00131",cytosol,Day),
  catalyst(5392,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5401),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00363",cytosol,Day),
  catalyst(5401,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00459",cytosol,Day) :-
  not exclude(5401),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00363",cytosol,Day),
  catalyst(5401,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(5402),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00459",cytosol,Day),
  catalyst(5402,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00363",cytosol,Day) :-
  not exclude(5402),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00459",cytosol,Day),
  catalyst(5402,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5411),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00705",cytosol,Day),
  catalyst(5411,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00458",cytosol,Day) :-
  not exclude(5411),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00705",cytosol,Day),
  catalyst(5411,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(5412),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00458",cytosol,Day),
  catalyst(5412,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00705",cytosol,Day) :-
  not exclude(5412),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00458",cytosol,Day),
  catalyst(5412,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5421),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01346",cytosol,Day),
  catalyst(5421,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00460",cytosol,Day) :-
  not exclude(5421),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01346",cytosol,Day),
  catalyst(5421,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(5422),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00460",cytosol,Day),
  catalyst(5422,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01346",cytosol,Day) :-
  not exclude(5422),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00460",cytosol,Day),
  catalyst(5422,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5431),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00361",cytosol,Day),
  catalyst(5431,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00286",cytosol,Day) :-
  not exclude(5431),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00361",cytosol,Day),
  catalyst(5431,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(5432),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00286",cytosol,Day),
  catalyst(5432,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00361",cytosol,Day) :-
  not exclude(5432),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00286",cytosol,Day),
  catalyst(5432,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5451),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00015",cytosol,Day),
  catalyst(5451,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00075",cytosol,Day) :-
  not exclude(5451),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00015",cytosol,Day),
  catalyst(5451,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(5452),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00075",cytosol,Day),
  catalyst(5452,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00015",cytosol,Day) :-
  not exclude(5452),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00075",cytosol,Day),
  catalyst(5452,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",mitochondrion,Day) :-
  not exclude(5471),
  Day >= 1,
  in_compartment(Experiment,"C00020",mitochondrion,Day),
  in_compartment(Experiment,"C00044",mitochondrion,Day),
  catalyst(5471,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00035",mitochondrion,Day) :-
  not exclude(5471),
  Day >= 1,
  in_compartment(Experiment,"C00020",mitochondrion,Day),
  in_compartment(Experiment,"C00044",mitochondrion,Day),
  catalyst(5471,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",mitochondrion,Day) :-
  not exclude(5472),
  Day >= 1,
  in_compartment(Experiment,"C00008",mitochondrion,Day),
  in_compartment(Experiment,"C00035",mitochondrion,Day),
  catalyst(5472,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00044",mitochondrion,Day) :-
  not exclude(5472),
  Day >= 1,
  in_compartment(Experiment,"C00008",mitochondrion,Day),
  in_compartment(Experiment,"C00035",mitochondrion,Day),
  catalyst(5472,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",mitochondrion,Day) :-
  not exclude(5481),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00020",mitochondrion,Day),
  catalyst(5481,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",mitochondrion,Day) :-
  not exclude(5482),
  Day >= 1,
  in_compartment(Experiment,"C00008",mitochondrion,Day),
  catalyst(5482,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",mitochondrion,Day) :-
  not exclude(5482),
  Day >= 1,
  in_compartment(Experiment,"C00008",mitochondrion,Day),
  catalyst(5482,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5491),
  Day >= 1,
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C00081",cytosol,Day),
  catalyst(5491,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00104",cytosol,Day) :-
  not exclude(5491),
  Day >= 1,
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C00081",cytosol,Day),
  catalyst(5491,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(5492),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00104",cytosol,Day),
  catalyst(5492,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00081",cytosol,Day) :-
  not exclude(5492),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00104",cytosol,Day),
  catalyst(5492,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5511),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  catalyst(5511,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(5512),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  catalyst(5512,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(5512),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  catalyst(5512,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5520),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00212",cytosol,Day),
  catalyst(5520,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(5520),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00212",cytosol,Day),
  catalyst(5520,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00121",cytosol,Day) :-
  not exclude(5540),
  Day >= 1,
  in_compartment(Experiment,"C00387",cytosol,Day),
  catalyst(5540,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00242",cytosol,Day) :-
  not exclude(5540),
  Day >= 1,
  in_compartment(Experiment,"C00387",cytosol,Day),
  catalyst(5540,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(5550),
  Day >= 1,
  in_compartment(Experiment,"C00119",cytosol,Day),
  in_compartment(Experiment,"C00385",cytosol,Day),
  catalyst(5550,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00655",cytosol,Day) :-
  not exclude(5550),
  Day >= 1,
  in_compartment(Experiment,"C00119",cytosol,Day),
  in_compartment(Experiment,"C00385",cytosol,Day),
  catalyst(5550,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5561),
  Day >= 1,
  in_compartment(Experiment,"C00385",cytosol,Day),
  in_compartment(Experiment,"C00620",cytosol,Day),
  catalyst(5561,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01762",cytosol,Day) :-
  not exclude(5561),
  Day >= 1,
  in_compartment(Experiment,"C00385",cytosol,Day),
  in_compartment(Experiment,"C00620",cytosol,Day),
  catalyst(5561,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00385",cytosol,Day) :-
  not exclude(5562),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C01762",cytosol,Day),
  catalyst(5562,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00620",cytosol,Day) :-
  not exclude(5562),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C01762",cytosol,Day),
  catalyst(5562,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5581),
  Day >= 1,
  in_compartment(Experiment,"C00147",cytosol,Day),
  in_compartment(Experiment,"C00620",cytosol,Day),
  catalyst(5581,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00212",cytosol,Day) :-
  not exclude(5581),
  Day >= 1,
  in_compartment(Experiment,"C00147",cytosol,Day),
  in_compartment(Experiment,"C00620",cytosol,Day),
  catalyst(5581,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00147",cytosol,Day) :-
  not exclude(5582),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00212",cytosol,Day),
  catalyst(5582,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00620",cytosol,Day) :-
  not exclude(5582),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00212",cytosol,Day),
  catalyst(5582,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5591),
  Day >= 1,
  in_compartment(Experiment,"C00262",cytosol,Day),
  in_compartment(Experiment,"C00620",cytosol,Day),
  catalyst(5591,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00294",cytosol,Day) :-
  not exclude(5591),
  Day >= 1,
  in_compartment(Experiment,"C00262",cytosol,Day),
  in_compartment(Experiment,"C00620",cytosol,Day),
  catalyst(5591,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00262",cytosol,Day) :-
  not exclude(5592),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00294",cytosol,Day),
  catalyst(5592,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00620",cytosol,Day) :-
  not exclude(5592),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00294",cytosol,Day),
  catalyst(5592,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00242",cytosol,Day) :-
  not exclude(5601),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00330",cytosol,Day),
  catalyst(5601,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03496",cytosol,Day) :-
  not exclude(5601),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00330",cytosol,Day),
  catalyst(5601,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5602),
  Day >= 1,
  in_compartment(Experiment,"C00242",cytosol,Day),
  in_compartment(Experiment,"C03496",cytosol,Day),
  catalyst(5602,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00330",cytosol,Day) :-
  not exclude(5602),
  Day >= 1,
  in_compartment(Experiment,"C00242",cytosol,Day),
  in_compartment(Experiment,"C03496",cytosol,Day),
  catalyst(5602,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00147",cytosol,Day) :-
  not exclude(5611),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00559",cytosol,Day),
  catalyst(5611,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03496",cytosol,Day) :-
  not exclude(5611),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00559",cytosol,Day),
  catalyst(5611,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5612),
  Day >= 1,
  in_compartment(Experiment,"C00147",cytosol,Day),
  in_compartment(Experiment,"C03496",cytosol,Day),
  catalyst(5612,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00559",cytosol,Day) :-
  not exclude(5612),
  Day >= 1,
  in_compartment(Experiment,"C00147",cytosol,Day),
  in_compartment(Experiment,"C03496",cytosol,Day),
  catalyst(5612,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00262",cytosol,Day) :-
  not exclude(5621),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C05512",cytosol,Day),
  catalyst(5621,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03496",cytosol,Day) :-
  not exclude(5621),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C05512",cytosol,Day),
  catalyst(5621,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5622),
  Day >= 1,
  in_compartment(Experiment,"C00262",cytosol,Day),
  in_compartment(Experiment,"C03496",cytosol,Day),
  catalyst(5622,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05512",cytosol,Day) :-
  not exclude(5622),
  Day >= 1,
  in_compartment(Experiment,"C00262",cytosol,Day),
  in_compartment(Experiment,"C03496",cytosol,Day),
  catalyst(5622,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(5630),
  Day >= 1,
  in_compartment(Experiment,"C00559",cytosol,Day),
  catalyst(5630,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05512",cytosol,Day) :-
  not exclude(5630),
  Day >= 1,
  in_compartment(Experiment,"C00559",cytosol,Day),
  catalyst(5630,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(5640),
  Day >= 1,
  in_compartment(Experiment,"C00212",cytosol,Day),
  catalyst(5640,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00294",cytosol,Day) :-
  not exclude(5640),
  Day >= 1,
  in_compartment(Experiment,"C00212",cytosol,Day),
  catalyst(5640,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01168",cytosol,Day) :-
  not exclude(5661),
  Day >= 1,
  in_compartment(Experiment,"C00106",cytosol,Day),
  in_compartment(Experiment,"C00117",cytosol,Day),
  catalyst(5661,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00106",cytosol,Day) :-
  not exclude(5662),
  Day >= 1,
  in_compartment(Experiment,"C01168",cytosol,Day),
  catalyst(5662,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00117",cytosol,Day) :-
  not exclude(5662),
  Day >= 1,
  in_compartment(Experiment,"C01168",cytosol,Day),
  catalyst(5662,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(5691),
  Day >= 1,
  in_compartment(Experiment,"C00239",cytosol,Day),
  catalyst(5691,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00365",cytosol,Day) :-
  not exclude(5691),
  Day >= 1,
  in_compartment(Experiment,"C00239",cytosol,Day),
  catalyst(5691,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00239",cytosol,Day) :-
  not exclude(5692),
  Day >= 1,
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00365",cytosol,Day),
  catalyst(5692,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5701),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00055",cytosol,Day),
  catalyst(5701,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00112",cytosol,Day) :-
  not exclude(5701),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00055",cytosol,Day),
  catalyst(5701,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(5702),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00112",cytosol,Day),
  catalyst(5702,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00055",cytosol,Day) :-
  not exclude(5702),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00112",cytosol,Day),
  catalyst(5702,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5711),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00239",cytosol,Day),
  catalyst(5711,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00705",cytosol,Day) :-
  not exclude(5711),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00239",cytosol,Day),
  catalyst(5711,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(5712),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00705",cytosol,Day),
  catalyst(5712,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00239",cytosol,Day) :-
  not exclude(5712),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00705",cytosol,Day),
  catalyst(5712,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(5730),
  Day >= 1,
  in_compartment(Experiment,"C00460",cytosol,Day),
  catalyst(5730,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00365",cytosol,Day) :-
  not exclude(5730),
  Day >= 1,
  in_compartment(Experiment,"C00460",cytosol,Day),
  catalyst(5730,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(5750),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00343",cytosol,Day),
  catalyst(5750,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00342",cytosol,Day) :-
  not exclude(5750),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00343",cytosol,Day),
  catalyst(5750,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(5770),
  Day >= 1,
  in_compartment(Experiment,"C00881",cytosol,Day),
  catalyst(5770,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00526",cytosol,Day) :-
  not exclude(5770),
  Day >= 1,
  in_compartment(Experiment,"C00881",cytosol,Day),
  catalyst(5770,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(5780),
  Day >= 1,
  in_compartment(Experiment,"C00475",cytosol,Day),
  catalyst(5780,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00299",cytosol,Day) :-
  not exclude(5780),
  Day >= 1,
  in_compartment(Experiment,"C00475",cytosol,Day),
  catalyst(5780,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00106",cytosol,Day) :-
  not exclude(5801),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00526",cytosol,Day),
  catalyst(5801,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03496",cytosol,Day) :-
  not exclude(5801),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00526",cytosol,Day),
  catalyst(5801,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5802),
  Day >= 1,
  in_compartment(Experiment,"C00106",cytosol,Day),
  in_compartment(Experiment,"C03496",cytosol,Day),
  catalyst(5802,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00526",cytosol,Day) :-
  not exclude(5802),
  Day >= 1,
  in_compartment(Experiment,"C00106",cytosol,Day),
  in_compartment(Experiment,"C03496",cytosol,Day),
  catalyst(5802,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00035",cytosol,Day) :-
  not exclude(5830),
  Day >= 1,
  in_compartment(Experiment,"C00044",cytosol,Day),
  in_compartment(Experiment,"C00299",cytosol,Day),
  catalyst(5830,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00105",cytosol,Day) :-
  not exclude(5830),
  Day >= 1,
  in_compartment(Experiment,"C00044",cytosol,Day),
  in_compartment(Experiment,"C00299",cytosol,Day),
  catalyst(5830,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(5840),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00214",cytosol,Day),
  catalyst(5840,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00364",cytosol,Day) :-
  not exclude(5840),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00214",cytosol,Day),
  catalyst(5840,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(5880),
  Day >= 1,
  in_compartment(Experiment,"C01103",cytosol,Day),
  catalyst(5880,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00105",cytosol,Day) :-
  not exclude(5880),
  Day >= 1,
  in_compartment(Experiment,"C01103",cytosol,Day),
  catalyst(5880,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00027",cytosol,Day) :-
  not exclude(5911),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00337",cytosol,Day),
  catalyst(5911,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00295",cytosol,Day) :-
  not exclude(5911),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00337",cytosol,Day),
  catalyst(5911,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",cytosol,Day) :-
  not exclude(5912),
  Day >= 1,
  in_compartment(Experiment,"C00027",cytosol,Day),
  in_compartment(Experiment,"C00295",cytosol,Day),
  catalyst(5912,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00337",cytosol,Day) :-
  not exclude(5912),
  Day >= 1,
  in_compartment(Experiment,"C00027",cytosol,Day),
  in_compartment(Experiment,"C00295",cytosol,Day),
  catalyst(5912,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00337",cytosol,Day) :-
  not exclude(5921),
  Day >= 1,
  in_compartment(Experiment,"C00438",cytosol,Day),
  catalyst(5921,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00438",cytosol,Day) :-
  not exclude(5922),
  Day >= 1,
  in_compartment(Experiment,"C00337",cytosol,Day),
  catalyst(5922,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5930),
  Day >= 1,
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C00169",cytosol,Day),
  catalyst(5930,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00438",cytosol,Day) :-
  not exclude(5930),
  Day >= 1,
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C00169",cytosol,Day),
  catalyst(5930,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5940),
  Day >= 1,
  in_compartment(Experiment,"C00035",cytosol,Day),
  in_compartment(Experiment,"C00044",cytosol,Day),
  catalyst(5940,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01261",cytosol,Day) :-
  not exclude(5940),
  Day >= 1,
  in_compartment(Experiment,"C00035",cytosol,Day),
  in_compartment(Experiment,"C00044",cytosol,Day),
  catalyst(5940,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(5960),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00008",cytosol,Day),
  catalyst(5960,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01260",cytosol,Day) :-
  not exclude(5960),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00008",cytosol,Day),
  catalyst(5960,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00055",cytosol,Day) :-
  not exclude(5970),
  Day >= 1,
  in_compartment(Experiment,"C00941",cytosol,Day),
  catalyst(5970,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00130",cytosol,Day) :-
  not exclude(5990),
  Day >= 1,
  in_compartment(Experiment,"C00943",cytosol,Day),
  catalyst(5990,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(6010),
  Day >= 1,
  in_compartment(Experiment,"C00575",cytosol,Day),
  catalyst(6010,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(6020),
  Day >= 1,
  in_compartment(Experiment,"C00020",cytosol,Day),
  catalyst(6020,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00130",cytosol,Day) :-
  not exclude(6020),
  Day >= 1,
  in_compartment(Experiment,"C00020",cytosol,Day),
  catalyst(6020,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(6030),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00655",cytosol,Day),
  catalyst(6030,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(6030),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00655",cytosol,Day),
  catalyst(6030,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(6030),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00655",cytosol,Day),
  catalyst(6030,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00144",cytosol,Day) :-
  not exclude(6030),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00655",cytosol,Day),
  catalyst(6030,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(6040),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00130",cytosol,Day),
  catalyst(6040,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00655",cytosol,Day) :-
  not exclude(6040),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00130",cytosol,Day),
  catalyst(6040,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(6051),
  Day >= 1,
  in_compartment(Experiment,"C03794",cytosol,Day),
  catalyst(6051,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00122",cytosol,Day) :-
  not exclude(6051),
  Day >= 1,
  in_compartment(Experiment,"C03794",cytosol,Day),
  catalyst(6051,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03794",cytosol,Day) :-
  not exclude(6052),
  Day >= 1,
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C00122",cytosol,Day),
  catalyst(6052,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00130",cytosol,Day) :-
  not exclude(6071),
  Day >= 1,
  in_compartment(Experiment,"C04734",cytosol,Day),
  catalyst(6071,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04734",cytosol,Day) :-
  not exclude(6072),
  Day >= 1,
  in_compartment(Experiment,"C00130",cytosol,Day),
  catalyst(6072,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00101",cytosol,Day) :-
  not exclude(6081),
  Day >= 1,
  in_compartment(Experiment,"C00234",cytosol,Day),
  in_compartment(Experiment,"C04677",cytosol,Day),
  catalyst(6081,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04734",cytosol,Day) :-
  not exclude(6081),
  Day >= 1,
  in_compartment(Experiment,"C00234",cytosol,Day),
  in_compartment(Experiment,"C04677",cytosol,Day),
  catalyst(6081,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00234",cytosol,Day) :-
  not exclude(6082),
  Day >= 1,
  in_compartment(Experiment,"C00101",cytosol,Day),
  in_compartment(Experiment,"C04734",cytosol,Day),
  catalyst(6082,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04677",cytosol,Day) :-
  not exclude(6082),
  Day >= 1,
  in_compartment(Experiment,"C00101",cytosol,Day),
  in_compartment(Experiment,"C04734",cytosol,Day),
  catalyst(6082,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00122",cytosol,Day) :-
  not exclude(6091),
  Day >= 1,
  in_compartment(Experiment,"C04823",cytosol,Day),
  catalyst(6091,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04677",cytosol,Day) :-
  not exclude(6091),
  Day >= 1,
  in_compartment(Experiment,"C04823",cytosol,Day),
  catalyst(6091,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04823",cytosol,Day) :-
  not exclude(6092),
  Day >= 1,
  in_compartment(Experiment,"C00122",cytosol,Day),
  in_compartment(Experiment,"C04677",cytosol,Day),
  catalyst(6092,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(6120),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C04640",cytosol,Day),
  catalyst(6120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(6120),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C04640",cytosol,Day),
  catalyst(6120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03373",cytosol,Day) :-
  not exclude(6120),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C04640",cytosol,Day),
  catalyst(6120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00101",cytosol,Day) :-
  not exclude(6140),
  Day >= 1,
  in_compartment(Experiment,"C00234",cytosol,Day),
  in_compartment(Experiment,"C03838",cytosol,Day),
  catalyst(6140,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04376",cytosol,Day) :-
  not exclude(6140),
  Day >= 1,
  in_compartment(Experiment,"C00234",cytosol,Day),
  in_compartment(Experiment,"C03838",cytosol,Day),
  catalyst(6140,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(6151),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00037",cytosol,Day),
  in_compartment(Experiment,"C03090",cytosol,Day),
  catalyst(6151,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(6151),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00037",cytosol,Day),
  in_compartment(Experiment,"C03090",cytosol,Day),
  catalyst(6151,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03838",cytosol,Day) :-
  not exclude(6151),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00037",cytosol,Day),
  in_compartment(Experiment,"C03090",cytosol,Day),
  catalyst(6151,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(6152),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C03838",cytosol,Day),
  catalyst(6152,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00037",cytosol,Day) :-
  not exclude(6152),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C03838",cytosol,Day),
  catalyst(6152,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03090",cytosol,Day) :-
  not exclude(6152),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C03838",cytosol,Day),
  catalyst(6152,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(6160),
  Day >= 1,
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00119",cytosol,Day),
  catalyst(6160,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(6160),
  Day >= 1,
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00119",cytosol,Day),
  catalyst(6160,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03090",cytosol,Day) :-
  not exclude(6160),
  Day >= 1,
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00119",cytosol,Day),
  catalyst(6160,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(6181),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00362",cytosol,Day),
  catalyst(6181,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00361",cytosol,Day) :-
  not exclude(6181),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00362",cytosol,Day),
  catalyst(6181,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(6182),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00361",cytosol,Day),
  catalyst(6182,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00362",cytosol,Day) :-
  not exclude(6182),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00361",cytosol,Day),
  catalyst(6182,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(6191),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00144",cytosol,Day),
  catalyst(6191,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00035",cytosol,Day) :-
  not exclude(6191),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00144",cytosol,Day),
  catalyst(6191,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(6192),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00035",cytosol,Day),
  catalyst(6192,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00144",cytosol,Day) :-
  not exclude(6192),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00035",cytosol,Day),
  catalyst(6192,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(6211),
  Day >= 1,
  in_compartment(Experiment,"C00603",cytosol,Day),
  catalyst(6211,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(6211),
  Day >= 1,
  in_compartment(Experiment,"C00603",cytosol,Day),
  catalyst(6211,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00048",cytosol,Day) :-
  not exclude(6211),
  Day >= 1,
  in_compartment(Experiment,"C00603",cytosol,Day),
  catalyst(6211,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00603",cytosol,Day) :-
  not exclude(6212),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00048",cytosol,Day),
  catalyst(6212,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(6241),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00117",cytosol,Day),
  catalyst(6241,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00119",cytosol,Day) :-
  not exclude(6241),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00117",cytosol,Day),
  catalyst(6241,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(6242),
  Day >= 1,
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C00119",cytosol,Day),
  catalyst(6242,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00117",cytosol,Day) :-
  not exclude(6242),
  Day >= 1,
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C00119",cytosol,Day),
  catalyst(6242,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",cytosol,Day) :-
  not exclude(6250),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C05437",cytosol,Day),
  catalyst(6250,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01694",cytosol,Day) :-
  not exclude(6250),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C05437",cytosol,Day),
  catalyst(6250,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(6260),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"MZYMST",cytosol,Day),
  catalyst(6260,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(6260),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"MZYMST",cytosol,Day),
  catalyst(6260,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(6260),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"MZYMST",cytosol,Day),
  catalyst(6260,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05437",cytosol,Day) :-
  not exclude(6260),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"MZYMST",cytosol,Day),
  catalyst(6260,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(6270),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C01724",cytosol,Day),
  catalyst(6270,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(6270),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C01724",cytosol,Day),
  catalyst(6270,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(6270),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C01724",cytosol,Day),
  catalyst(6270,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"MZYMST",cytosol,Day) :-
  not exclude(6270),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C01724",cytosol,Day),
  catalyst(6270,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(6290),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"ERTROL",cytosol,Day),
  catalyst(6290,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"ERTEOL",cytosol,Day) :-
  not exclude(6290),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"ERTROL",cytosol,Day),
  catalyst(6290,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(6300),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"EPST",cytosol,Day),
  catalyst(6300,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"ERTROL",cytosol,Day) :-
  not exclude(6300),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"EPST",cytosol,Day),
  catalyst(6300,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"EPST",cytosol,Day) :-
  not exclude(6310),
  Day >= 1,
  in_compartment(Experiment,"C08817",cytosol,Day),
  catalyst(6310,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",cytosol,Day) :-
  not exclude(6320),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C05437",cytosol,Day),
  catalyst(6320,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C08817",cytosol,Day) :-
  not exclude(6320),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C05437",cytosol,Day),
  catalyst(6320,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(6330),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"IIZYMST",cytosol,Day),
  catalyst(6330,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05437",cytosol,Day) :-
  not exclude(6330),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"IIZYMST",cytosol,Day),
  catalyst(6330,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(6340),
  Day >= 1,
  in_compartment(Experiment,"IZYMST",cytosol,Day),
  catalyst(6340,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"IIZYMST",cytosol,Day) :-
  not exclude(6340),
  Day >= 1,
  in_compartment(Experiment,"IZYMST",cytosol,Day),
  catalyst(6340,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(6360),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"IIMZYMST",cytosol,Day),
  catalyst(6360,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"MZYMST",cytosol,Day) :-
  not exclude(6360),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"IIMZYMST",cytosol,Day),
  catalyst(6360,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(6370),
  Day >= 1,
  in_compartment(Experiment,"IMZYMST",cytosol,Day),
  catalyst(6370,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"IIMZYMST",cytosol,Day) :-
  not exclude(6370),
  Day >= 1,
  in_compartment(Experiment,"IMZYMST",cytosol,Day),
  catalyst(6370,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(6390),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"IGST",cytosol,Day),
  catalyst(6390,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"DMZYMST",cytosol,Day) :-
  not exclude(6390),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"IGST",cytosol,Day),
  catalyst(6390,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03161",cytosol,Day) :-
  not exclude(6400),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C01724",cytosol,Day),
  in_compartment(Experiment,"C03024",cytosol,Day),
  catalyst(6400,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"IGST",cytosol,Day) :-
  not exclude(6400),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C01724",cytosol,Day),
  in_compartment(Experiment,"C03024",cytosol,Day),
  catalyst(6400,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01724",cytosol,Day) :-
  not exclude(6410),
  Day >= 1,
  in_compartment(Experiment,"C01054",cytosol,Day),
  catalyst(6410,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(6430),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00448",cytosol,Day),
  catalyst(6430,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00751",cytosol,Day) :-
  not exclude(6430),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00448",cytosol,Day),
  catalyst(6430,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(6440),
  Day >= 1,
  in_compartment(Experiment,"C00129",cytosol,Day),
  in_compartment(Experiment,"C00341",cytosol,Day),
  catalyst(6440,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00448",cytosol,Day) :-
  not exclude(6440),
  Day >= 1,
  in_compartment(Experiment,"C00129",cytosol,Day),
  in_compartment(Experiment,"C00341",cytosol,Day),
  catalyst(6440,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(6450),
  Day >= 1,
  in_compartment(Experiment,"C00129",cytosol,Day),
  in_compartment(Experiment,"C00235",cytosol,Day),
  catalyst(6450,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00341",cytosol,Day) :-
  not exclude(6450),
  Day >= 1,
  in_compartment(Experiment,"C00129",cytosol,Day),
  in_compartment(Experiment,"C00235",cytosol,Day),
  catalyst(6450,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00235",cytosol,Day) :-
  not exclude(6461),
  Day >= 1,
  in_compartment(Experiment,"C00129",cytosol,Day),
  catalyst(6461,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00129",cytosol,Day) :-
  not exclude(6462),
  Day >= 1,
  in_compartment(Experiment,"C00235",cytosol,Day),
  catalyst(6462,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(6470),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01143",cytosol,Day),
  catalyst(6470,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(6470),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01143",cytosol,Day),
  catalyst(6470,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(6470),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01143",cytosol,Day),
  catalyst(6470,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00129",cytosol,Day) :-
  not exclude(6470),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01143",cytosol,Day),
  catalyst(6470,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(6480),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01107",cytosol,Day),
  catalyst(6480,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01143",cytosol,Day) :-
  not exclude(6480),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01107",cytosol,Day),
  catalyst(6480,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00015",cytosol,Day) :-
  not exclude(6490),
  Day >= 1,
  in_compartment(Experiment,"C00075",cytosol,Day),
  in_compartment(Experiment,"C00418",cytosol,Day),
  catalyst(6490,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01107",cytosol,Day) :-
  not exclude(6490),
  Day >= 1,
  in_compartment(Experiment,"C00075",cytosol,Day),
  in_compartment(Experiment,"C00418",cytosol,Day),
  catalyst(6490,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00035",cytosol,Day) :-
  not exclude(6500),
  Day >= 1,
  in_compartment(Experiment,"C00044",cytosol,Day),
  in_compartment(Experiment,"C00418",cytosol,Day),
  catalyst(6500,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01107",cytosol,Day) :-
  not exclude(6500),
  Day >= 1,
  in_compartment(Experiment,"C00044",cytosol,Day),
  in_compartment(Experiment,"C00418",cytosol,Day),
  catalyst(6500,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00112",cytosol,Day) :-
  not exclude(6510),
  Day >= 1,
  in_compartment(Experiment,"C00063",cytosol,Day),
  in_compartment(Experiment,"C00418",cytosol,Day),
  catalyst(6510,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01107",cytosol,Day) :-
  not exclude(6510),
  Day >= 1,
  in_compartment(Experiment,"C00063",cytosol,Day),
  in_compartment(Experiment,"C00418",cytosol,Day),
  catalyst(6510,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(6520),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00418",cytosol,Day),
  catalyst(6520,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01107",cytosol,Day) :-
  not exclude(6520),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00418",cytosol,Day),
  catalyst(6520,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(6531),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00418",cytosol,Day),
  catalyst(6531,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00356",cytosol,Day) :-
  not exclude(6531),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00418",cytosol,Day),
  catalyst(6531,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(6532),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00356",cytosol,Day),
  catalyst(6532,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(6532),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00356",cytosol,Day),
  catalyst(6532,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00418",cytosol,Day) :-
  not exclude(6532),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00356",cytosol,Day),
  catalyst(6532,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00024",cytosol,Day) :-
  not exclude(6541),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00356",cytosol,Day),
  catalyst(6541,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00332",cytosol,Day) :-
  not exclude(6541),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00356",cytosol,Day),
  catalyst(6541,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(6542),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00332",cytosol,Day),
  catalyst(6542,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00356",cytosol,Day) :-
  not exclude(6542),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00332",cytosol,Day),
  catalyst(6542,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00346",cytosol,Day) :-
  not exclude(6550),
  Day >= 1,
  in_compartment(Experiment,"C01120",cytosol,Day),
  catalyst(6550,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C16A",cytosol,Day) :-
  not exclude(6550),
  Day >= 1,
  in_compartment(Experiment,"C01120",cytosol,Day),
  catalyst(6550,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(6560),
  Day >= 1,
  in_compartment(Experiment,"C01120",cytosol,Day),
  catalyst(6560,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00836",cytosol,Day) :-
  not exclude(6560),
  Day >= 1,
  in_compartment(Experiment,"C01120",cytosol,Day),
  catalyst(6560,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(6570),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"PSPH",cytosol,Day),
  catalyst(6570,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"PHSP",cytosol,Day) :-
  not exclude(6570),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"PSPH",cytosol,Day),
  catalyst(6570,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(6580),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00836",cytosol,Day),
  catalyst(6580,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01120",cytosol,Day) :-
  not exclude(6580),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00836",cytosol,Day),
  catalyst(6580,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"IPC",cytosol,Day) :-
  not exclude(6610),
  Day >= 1,
  in_compartment(Experiment,"C01194",cytosol,Day),
  in_compartment(Experiment,"CER3",cytosol,Day),
  catalyst(6610,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(6620),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"CER2",cytosol,Day),
  catalyst(6620,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"CER3",cytosol,Day) :-
  not exclude(6620),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"CER2",cytosol,Day),
  catalyst(6620,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(6640),
  Day >= 1,
  in_compartment(Experiment,"C260COA",cytosol,Day),
  in_compartment(Experiment,"PSPH",cytosol,Day),
  catalyst(6640,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"CER2",cytosol,Day) :-
  not exclude(6640),
  Day >= 1,
  in_compartment(Experiment,"C260COA",cytosol,Day),
  in_compartment(Experiment,"PSPH",cytosol,Day),
  catalyst(6640,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(6650),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00836",cytosol,Day),
  catalyst(6650,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"PSPH",cytosol,Day) :-
  not exclude(6650),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00836",cytosol,Day),
  catalyst(6650,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(6680),
  Day >= 1,
  in_compartment(Experiment,"DGPP",cytosol,Day),
  catalyst(6680,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00416",cytosol,Day) :-
  not exclude(6680),
  Day >= 1,
  in_compartment(Experiment,"DGPP",cytosol,Day),
  catalyst(6680,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",mitochondrion,Day) :-
  not exclude(6710),
  Day >= 1,
  in_compartment(Experiment,"C03892",mitochondrion,Day),
  catalyst(6710,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00344",mitochondrion,Day) :-
  not exclude(6710),
  Day >= 1,
  in_compartment(Experiment,"C03892",mitochondrion,Day),
  catalyst(6710,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00165",cytosol,Day) :-
  not exclude(6730),
  Day >= 1,
  in_compartment(Experiment,"C04637",cytosol,Day),
  catalyst(6730,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01245",cytosol,Day) :-
  not exclude(6730),
  Day >= 1,
  in_compartment(Experiment,"C04637",cytosol,Day),
  catalyst(6730,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(6740),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01277",cytosol,Day),
  catalyst(6740,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04637",cytosol,Day) :-
  not exclude(6740),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01277",cytosol,Day),
  catalyst(6740,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(6760),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01194",cytosol,Day),
  catalyst(6760,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04549",cytosol,Day) :-
  not exclude(6760),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01194",cytosol,Day),
  catalyst(6760,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(6780),
  Day >= 1,
  in_compartment(Experiment,"C01177",cytosol,Day),
  catalyst(6780,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00137",cytosol,Day) :-
  not exclude(6780),
  Day >= 1,
  in_compartment(Experiment,"C01177",cytosol,Day),
  catalyst(6780,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01177",cytosol,Day) :-
  not exclude(6790),
  Day >= 1,
  in_compartment(Experiment,"C00668",cytosol,Day),
  catalyst(6790,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00055",cytosol,Day) :-
  not exclude(6801),
  Day >= 1,
  in_compartment(Experiment,"C00165",cytosol,Day),
  in_compartment(Experiment,"C00570",cytosol,Day),
  catalyst(6801,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00350",cytosol,Day) :-
  not exclude(6801),
  Day >= 1,
  in_compartment(Experiment,"C00165",cytosol,Day),
  in_compartment(Experiment,"C00570",cytosol,Day),
  catalyst(6801,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00165",cytosol,Day) :-
  not exclude(6802),
  Day >= 1,
  in_compartment(Experiment,"C00055",cytosol,Day),
  in_compartment(Experiment,"C00350",cytosol,Day),
  catalyst(6802,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00570",cytosol,Day) :-
  not exclude(6802),
  Day >= 1,
  in_compartment(Experiment,"C00055",cytosol,Day),
  in_compartment(Experiment,"C00350",cytosol,Day),
  catalyst(6802,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(6810),
  Day >= 1,
  in_compartment(Experiment,"C00063",cytosol,Day),
  in_compartment(Experiment,"C00346",cytosol,Day),
  catalyst(6810,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00570",cytosol,Day) :-
  not exclude(6810),
  Day >= 1,
  in_compartment(Experiment,"C00063",cytosol,Day),
  in_compartment(Experiment,"C00346",cytosol,Day),
  catalyst(6810,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(6820),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00189",cytosol,Day),
  catalyst(6820,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00346",cytosol,Day) :-
  not exclude(6820),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00189",cytosol,Day),
  catalyst(6820,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00055",cytosol,Day) :-
  not exclude(6830),
  Day >= 1,
  in_compartment(Experiment,"C00165",cytosol,Day),
  in_compartment(Experiment,"C00307",cytosol,Day),
  catalyst(6830,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00157",cytosol,Day) :-
  not exclude(6830),
  Day >= 1,
  in_compartment(Experiment,"C00165",cytosol,Day),
  in_compartment(Experiment,"C00307",cytosol,Day),
  catalyst(6830,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(6840),
  Day >= 1,
  in_compartment(Experiment,"C00063",cytosol,Day),
  in_compartment(Experiment,"C00588",cytosol,Day),
  catalyst(6840,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00307",cytosol,Day) :-
  not exclude(6840),
  Day >= 1,
  in_compartment(Experiment,"C00063",cytosol,Day),
  in_compartment(Experiment,"C00588",cytosol,Day),
  catalyst(6840,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(6850),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00114",cytosol,Day),
  catalyst(6850,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00588",cytosol,Day) :-
  not exclude(6850),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00114",cytosol,Day),
  catalyst(6850,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",cytosol,Day) :-
  not exclude(6860),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C04308",cytosol,Day),
  catalyst(6860,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00157",cytosol,Day) :-
  not exclude(6860),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C04308",cytosol,Day),
  catalyst(6860,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",cytosol,Day) :-
  not exclude(6870),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C01241",cytosol,Day),
  catalyst(6870,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04308",cytosol,Day) :-
  not exclude(6870),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C01241",cytosol,Day),
  catalyst(6870,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(6900),
  Day >= 1,
  in_compartment(Experiment,"C02737",cytosol,Day),
  catalyst(6900,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00350",cytosol,Day) :-
  not exclude(6900),
  Day >= 1,
  in_compartment(Experiment,"C02737",cytosol,Day),
  catalyst(6900,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(6931),
  Day >= 1,
  in_compartment(Experiment,"C00063",cytosol,Day),
  in_compartment(Experiment,"C00416",cytosol,Day),
  catalyst(6931,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00269",cytosol,Day) :-
  not exclude(6931),
  Day >= 1,
  in_compartment(Experiment,"C00063",cytosol,Day),
  in_compartment(Experiment,"C00416",cytosol,Day),
  catalyst(6931,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00063",cytosol,Day) :-
  not exclude(6932),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00269",cytosol,Day),
  catalyst(6932,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00416",cytosol,Day) :-
  not exclude(6932),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00269",cytosol,Day),
  catalyst(6932,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",mitochondrion,Day) :-
  not exclude(6941),
  Day >= 1,
  in_compartment(Experiment,"C00063",mitochondrion,Day),
  in_compartment(Experiment,"C00416",mitochondrion,Day),
  catalyst(6941,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00269",mitochondrion,Day) :-
  not exclude(6941),
  Day >= 1,
  in_compartment(Experiment,"C00063",mitochondrion,Day),
  in_compartment(Experiment,"C00416",mitochondrion,Day),
  catalyst(6941,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00063",mitochondrion,Day) :-
  not exclude(6942),
  Day >= 1,
  in_compartment(Experiment,"C00013",mitochondrion,Day),
  in_compartment(Experiment,"C00269",mitochondrion,Day),
  catalyst(6942,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00416",mitochondrion,Day) :-
  not exclude(6942),
  Day >= 1,
  in_compartment(Experiment,"C00013",mitochondrion,Day),
  in_compartment(Experiment,"C00269",mitochondrion,Day),
  catalyst(6942,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(6950),
  Day >= 1,
  in_compartment(Experiment,"C01203",cytosol,Day),
  in_compartment(Experiment,"C03849",cytosol,Day),
  in_compartment(Experiment,"C04088",cytosol,Day),
  in_compartment(Experiment,"C05223",cytosol,Day),
  in_compartment(Experiment,"C05755",cytosol,Day),
  in_compartment(Experiment,"C05764",cytosol,Day),
  in_compartment(Experiment,"C06253",cytosol,Day),
  in_compartment(Experiment,"C161ACP",cytosol,Day),
  in_compartment(Experiment,"C182ACP",cytosol,Day),
  catalyst(6950,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00416",cytosol,Day) :-
  not exclude(6950),
  Day >= 1,
  in_compartment(Experiment,"C01203",cytosol,Day),
  in_compartment(Experiment,"C03849",cytosol,Day),
  in_compartment(Experiment,"C04088",cytosol,Day),
  in_compartment(Experiment,"C05223",cytosol,Day),
  in_compartment(Experiment,"C05755",cytosol,Day),
  in_compartment(Experiment,"C05764",cytosol,Day),
  in_compartment(Experiment,"C06253",cytosol,Day),
  in_compartment(Experiment,"C161ACP",cytosol,Day),
  in_compartment(Experiment,"C182ACP",cytosol,Day),
  catalyst(6950,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(6960),
  Day >= 1,
  in_compartment(Experiment,"AT3P2",cytosol,Day),
  in_compartment(Experiment,"C00005",cytosol,Day),
  catalyst(6960,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03849",cytosol,Day) :-
  not exclude(6960),
  Day >= 1,
  in_compartment(Experiment,"AT3P2",cytosol,Day),
  in_compartment(Experiment,"C00005",cytosol,Day),
  catalyst(6960,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"AT3P2",cytosol,Day) :-
  not exclude(6970),
  Day >= 1,
  in_compartment(Experiment,"C00111",cytosol,Day),
  in_compartment(Experiment,"C01203",cytosol,Day),
  in_compartment(Experiment,"C04088",cytosol,Day),
  in_compartment(Experiment,"C05223",cytosol,Day),
  in_compartment(Experiment,"C05755",cytosol,Day),
  in_compartment(Experiment,"C05764",cytosol,Day),
  in_compartment(Experiment,"C06253",cytosol,Day),
  in_compartment(Experiment,"C161ACP",cytosol,Day),
  in_compartment(Experiment,"C182ACP",cytosol,Day),
  catalyst(6970,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(6970),
  Day >= 1,
  in_compartment(Experiment,"C00111",cytosol,Day),
  in_compartment(Experiment,"C01203",cytosol,Day),
  in_compartment(Experiment,"C04088",cytosol,Day),
  in_compartment(Experiment,"C05223",cytosol,Day),
  in_compartment(Experiment,"C05755",cytosol,Day),
  in_compartment(Experiment,"C05764",cytosol,Day),
  in_compartment(Experiment,"C06253",cytosol,Day),
  in_compartment(Experiment,"C161ACP",cytosol,Day),
  in_compartment(Experiment,"C182ACP",cytosol,Day),
  catalyst(6970,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(6980),
  Day >= 1,
  in_compartment(Experiment,"C00093",cytosol,Day),
  in_compartment(Experiment,"C01203",cytosol,Day),
  in_compartment(Experiment,"C04088",cytosol,Day),
  in_compartment(Experiment,"C05223",cytosol,Day),
  in_compartment(Experiment,"C05755",cytosol,Day),
  in_compartment(Experiment,"C05764",cytosol,Day),
  in_compartment(Experiment,"C06253",cytosol,Day),
  in_compartment(Experiment,"C161ACP",cytosol,Day),
  in_compartment(Experiment,"C182ACP",cytosol,Day),
  catalyst(6980,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03849",cytosol,Day) :-
  not exclude(6980),
  Day >= 1,
  in_compartment(Experiment,"C00093",cytosol,Day),
  in_compartment(Experiment,"C01203",cytosol,Day),
  in_compartment(Experiment,"C04088",cytosol,Day),
  in_compartment(Experiment,"C05223",cytosol,Day),
  in_compartment(Experiment,"C05755",cytosol,Day),
  in_compartment(Experiment,"C05764",cytosol,Day),
  in_compartment(Experiment,"C06253",cytosol,Day),
  in_compartment(Experiment,"C161ACP",cytosol,Day),
  in_compartment(Experiment,"C182ACP",cytosol,Day),
  catalyst(6980,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(6990),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C01530",cytosol,Day),
  catalyst(6990,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(6990),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C01530",cytosol,Day),
  catalyst(6990,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(6990),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C01530",cytosol,Day),
  catalyst(6990,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00024",cytosol,Day) :-
  not exclude(6990),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C01530",cytosol,Day),
  catalyst(6990,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01352",mitochondrion,Day) :-
  not exclude(6990),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C01530",cytosol,Day),
  catalyst(6990,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(7000),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C00249",cytosol,Day),
  catalyst(7000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(7000),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C00249",cytosol,Day),
  catalyst(7000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(7000),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C00249",cytosol,Day),
  catalyst(7000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00024",cytosol,Day) :-
  not exclude(7000),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C00249",cytosol,Day),
  catalyst(7000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01352",mitochondrion,Day) :-
  not exclude(7000),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C00249",cytosol,Day),
  catalyst(7000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"23DAACP",cytosol,Day) :-
  not exclude(7021),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  catalyst(7021,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(7021),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  catalyst(7021,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(7022),
  Day >= 1,
  in_compartment(Experiment,"23DAACP",cytosol,Day),
  in_compartment(Experiment,"C00004",cytosol,Day),
  catalyst(7022,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00173",cytosol,Day) :-
  not exclude(7022),
  Day >= 1,
  in_compartment(Experiment,"23DAACP",cytosol,Day),
  in_compartment(Experiment,"C00004",cytosol,Day),
  catalyst(7022,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"2HDACP",cytosol,Day) :-
  not exclude(7031),
  Day >= 1,
  in_compartment(Experiment,"C04633",cytosol,Day),
  catalyst(7031,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04633",cytosol,Day) :-
  not exclude(7032),
  Day >= 1,
  in_compartment(Experiment,"2HDACP",cytosol,Day),
  catalyst(7032,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(7060),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7060,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(7060),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7060,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(7060),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7060,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04088",cytosol,Day) :-
  not exclude(7060),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7060,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(7080),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7080,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(7080),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7080,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(7080),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7080,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05764",cytosol,Day) :-
  not exclude(7080),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7080,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(7090),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7090,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(7090),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7090,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(7090),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7090,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05761",cytosol,Day) :-
  not exclude(7090),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7090,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(7110),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7110,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(7110),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7110,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(7110),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7110,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05223",cytosol,Day) :-
  not exclude(7110),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7110,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(7120),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(7120),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(7120),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05755",cytosol,Day) :-
  not exclude(7120),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"3OACP",mitochondrion,Day) :-
  not exclude(7130),
  Day >= 1,
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7130,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(7130),
  Day >= 1,
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7130,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",mitochondrion,Day) :-
  not exclude(7130),
  Day >= 1,
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7130,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(7151),
  Day >= 1,
  in_compartment(Experiment,"C00083",cytosol,Day),
  in_compartment(Experiment,"C00229",cytosol,Day),
  catalyst(7151,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01209",cytosol,Day) :-
  not exclude(7151),
  Day >= 1,
  in_compartment(Experiment,"C00083",cytosol,Day),
  in_compartment(Experiment,"C00229",cytosol,Day),
  catalyst(7151,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00083",cytosol,Day) :-
  not exclude(7152),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7152,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(7152),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(7152,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(7161),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00024",cytosol,Day),
  catalyst(7161,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(7161),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00024",cytosol,Day),
  catalyst(7161,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00083",cytosol,Day) :-
  not exclude(7161),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00024",cytosol,Day),
  catalyst(7161,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(7162),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00083",cytosol,Day),
  catalyst(7162,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(7162),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00083",cytosol,Day),
  catalyst(7162,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00024",cytosol,Day) :-
  not exclude(7162),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00083",cytosol,Day),
  catalyst(7162,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",mitochondrion,Day) :-
  not exclude(7170),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7170,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(7170),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7170,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",mitochondrion,Day) :-
  not exclude(7170),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7170,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C182ACP",mitochondrion,Day) :-
  not exclude(7170),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7170,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",mitochondrion,Day) :-
  not exclude(7190),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7190,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(7190),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7190,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",mitochondrion,Day) :-
  not exclude(7190),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7190,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04088",mitochondrion,Day) :-
  not exclude(7190),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7190,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",mitochondrion,Day) :-
  not exclude(7220),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7220,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(7220),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7220,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",mitochondrion,Day) :-
  not exclude(7220),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7220,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05761",mitochondrion,Day) :-
  not exclude(7220),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7220,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",mitochondrion,Day) :-
  not exclude(7230),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7230,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(7230),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7230,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",mitochondrion,Day) :-
  not exclude(7230),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7230,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C06253",mitochondrion,Day) :-
  not exclude(7230),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7230,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",mitochondrion,Day) :-
  not exclude(7240),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7240,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(7240),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7240,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",mitochondrion,Day) :-
  not exclude(7240),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7240,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05223",mitochondrion,Day) :-
  not exclude(7240),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7240,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",mitochondrion,Day) :-
  not exclude(7250),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7250,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(7250),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7250,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",mitochondrion,Day) :-
  not exclude(7250),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7250,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05755",mitochondrion,Day) :-
  not exclude(7250),
  Day >= 1,
  in_compartment(Experiment,"C00005",mitochondrion,Day),
  in_compartment(Experiment,"C00173",mitochondrion,Day),
  in_compartment(Experiment,"C01209",mitochondrion,Day),
  catalyst(7250,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",mitochondrion,Day) :-
  not exclude(7260),
  Day >= 1,
  in_compartment(Experiment,"C00004",mitochondrion,Day),
  in_compartment(Experiment,"C01967",mitochondrion,Day),
  catalyst(7260,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00390",mitochondrion,Day) :-
  not exclude(7260),
  Day >= 1,
  in_compartment(Experiment,"C00004",mitochondrion,Day),
  in_compartment(Experiment,"C01967",mitochondrion,Day),
  catalyst(7260,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00024",cytosol,Day) :-
  not exclude(7290),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00264",cytosol,Day),
  catalyst(7290,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00040",cytosol,Day) :-
  not exclude(7290),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00264",cytosol,Day),
  catalyst(7290,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(7301),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00640",cytosol,Day),
  catalyst(7301,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00264",cytosol,Day) :-
  not exclude(7301),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00640",cytosol,Day),
  catalyst(7301,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(7302),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00264",cytosol,Day),
  catalyst(7302,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00640",cytosol,Day) :-
  not exclude(7302),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00264",cytosol,Day),
  catalyst(7302,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(7320),
  Day >= 1,
  in_compartment(Experiment,"C02938",cytosol,Day),
  catalyst(7320,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00954",cytosol,Day) :-
  not exclude(7320),
  Day >= 1,
  in_compartment(Experiment,"C02938",cytosol,Day),
  catalyst(7320,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(7350),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00058",cytosol,Day),
  catalyst(7350,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(7350),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00058",cytosol,Day),
  catalyst(7350,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",mitochondrion,Day) :-
  not exclude(7370),
  Day >= 1,
  in_compartment(Experiment,"C00125",mitochondrion,Day),
  in_compartment(Experiment,"C00186",mitochondrion,Day),
  catalyst(7370,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00126",mitochondrion,Day) :-
  not exclude(7370),
  Day >= 1,
  in_compartment(Experiment,"C00125",mitochondrion,Day),
  in_compartment(Experiment,"C00186",mitochondrion,Day),
  catalyst(7370,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",mitochondrion,Day) :-
  not exclude(7380),
  Day >= 1,
  in_compartment(Experiment,"C00008",mitochondrion,Day),
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  catalyst(7380,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",mitochondrion,Day) :-
  not exclude(7380),
  Day >= 1,
  in_compartment(Experiment,"C00008",mitochondrion,Day),
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  catalyst(7380,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00125",mitochondrion,Day) :-
  not exclude(7390),
  Day >= 1,
  in_compartment(Experiment,"C00007",mitochondrion,Day),
  in_compartment(Experiment,"C00080",mitochondrion,Day),
  in_compartment(Experiment,"C00126",mitochondrion,Day),
  catalyst(7390,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00126",mitochondrion,Day) :-
  not exclude(7400),
  Day >= 1,
  in_compartment(Experiment,"C00080",mitochondrion,Day),
  in_compartment(Experiment,"C00125",mitochondrion,Day),
  in_compartment(Experiment,"C00390",mitochondrion,Day),
  catalyst(7400,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01967",mitochondrion,Day) :-
  not exclude(7400),
  Day >= 1,
  in_compartment(Experiment,"C00080",mitochondrion,Day),
  in_compartment(Experiment,"C00125",mitochondrion,Day),
  in_compartment(Experiment,"C00390",mitochondrion,Day),
  catalyst(7400,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00016",mitochondrion,Day) :-
  not exclude(7411),
  Day >= 1,
  in_compartment(Experiment,"C01352",mitochondrion,Day),
  in_compartment(Experiment,"C01967",mitochondrion,Day),
  catalyst(7411,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00390",mitochondrion,Day) :-
  not exclude(7411),
  Day >= 1,
  in_compartment(Experiment,"C01352",mitochondrion,Day),
  in_compartment(Experiment,"C01967",mitochondrion,Day),
  catalyst(7411,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01352",mitochondrion,Day) :-
  not exclude(7412),
  Day >= 1,
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C00390",mitochondrion,Day),
  catalyst(7412,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01967",mitochondrion,Day) :-
  not exclude(7412),
  Day >= 1,
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C00390",mitochondrion,Day),
  catalyst(7412,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(7420),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00125",mitochondrion,Day),
  catalyst(7420,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00126",mitochondrion,Day) :-
  not exclude(7420),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00125",mitochondrion,Day),
  catalyst(7420,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(7430),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C01967",mitochondrion,Day),
  catalyst(7430,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00390",mitochondrion,Day) :-
  not exclude(7430),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C01967",mitochondrion,Day),
  catalyst(7430,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(7440),
  Day >= 1,
  in_compartment(Experiment,"C00058",cytosol,Day),
  in_compartment(Experiment,"C01967",mitochondrion,Day),
  catalyst(7440,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",medium,Day) :-
  not exclude(7440),
  Day >= 1,
  in_compartment(Experiment,"C00058",cytosol,Day),
  in_compartment(Experiment,"C01967",mitochondrion,Day),
  catalyst(7440,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00390",mitochondrion,Day) :-
  not exclude(7440),
  Day >= 1,
  in_compartment(Experiment,"C00058",cytosol,Day),
  in_compartment(Experiment,"C01967",mitochondrion,Day),
  catalyst(7440,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(7460),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  catalyst(7460,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00051",cytosol,Day) :-
  not exclude(7480),
  Day >= 1,
  in_compartment(Experiment,"C03451",cytosol,Day),
  catalyst(7480,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00256",cytosol,Day) :-
  not exclude(7480),
  Day >= 1,
  in_compartment(Experiment,"C03451",cytosol,Day),
  catalyst(7480,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",mitochondrion,Day) :-
  not exclude(7511),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00469",mitochondrion,Day),
  catalyst(7511,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00084",mitochondrion,Day) :-
  not exclude(7511),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00469",mitochondrion,Day),
  catalyst(7511,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",mitochondrion,Day) :-
  not exclude(7512),
  Day >= 1,
  in_compartment(Experiment,"C00004",mitochondrion,Day),
  in_compartment(Experiment,"C00084",mitochondrion,Day),
  catalyst(7512,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00469",mitochondrion,Day) :-
  not exclude(7512),
  Day >= 1,
  in_compartment(Experiment,"C00004",mitochondrion,Day),
  in_compartment(Experiment,"C00084",mitochondrion,Day),
  catalyst(7512,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",mitochondrion,Day) :-
  not exclude(7520),
  Day >= 1,
  in_compartment(Experiment,"C00024",mitochondrion,Day),
  in_compartment(Experiment,"C00026",mitochondrion,Day),
  catalyst(7520,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01251",mitochondrion,Day) :-
  not exclude(7520),
  Day >= 1,
  in_compartment(Experiment,"C00024",mitochondrion,Day),
  in_compartment(Experiment,"C00026",mitochondrion,Day),
  catalyst(7520,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(7530),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00026",cytosol,Day),
  catalyst(7530,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01251",cytosol,Day) :-
  not exclude(7530),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00026",cytosol,Day),
  catalyst(7530,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(7550),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(7550,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00084",cytosol,Day) :-
  not exclude(7550),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(7550,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00051",cytosol,Day) :-
  not exclude(7561),
  Day >= 1,
  in_compartment(Experiment,"C01031",cytosol,Day),
  catalyst(7561,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00058",cytosol,Day) :-
  not exclude(7561),
  Day >= 1,
  in_compartment(Experiment,"C01031",cytosol,Day),
  catalyst(7561,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01031",cytosol,Day) :-
  not exclude(7562),
  Day >= 1,
  in_compartment(Experiment,"C00051",cytosol,Day),
  in_compartment(Experiment,"C00058",cytosol,Day),
  catalyst(7562,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00015",cytosol,Day) :-
  not exclude(7590),
  Day >= 1,
  in_compartment(Experiment,"C00029",cytosol,Day),
  catalyst(7590,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00182",cytosol,Day) :-
  not exclude(7590),
  Day >= 1,
  in_compartment(Experiment,"C00029",cytosol,Day),
  catalyst(7590,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00103",cytosol,Day) :-
  not exclude(7600),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00182",cytosol,Day),
  catalyst(7600,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00267",cytosol,Day) :-
  not exclude(7610),
  Day >= 1,
  in_compartment(Experiment,"C01083",cytosol,Day),
  catalyst(7610,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(7620),
  Day >= 1,
  in_compartment(Experiment,"C00689",cytosol,Day),
  catalyst(7620,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01083",cytosol,Day) :-
  not exclude(7620),
  Day >= 1,
  in_compartment(Experiment,"C00689",cytosol,Day),
  catalyst(7620,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00015",cytosol,Day) :-
  not exclude(7630),
  Day >= 1,
  in_compartment(Experiment,"C00029",cytosol,Day),
  in_compartment(Experiment,"C00668",cytosol,Day),
  catalyst(7630,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00689",cytosol,Day) :-
  not exclude(7630),
  Day >= 1,
  in_compartment(Experiment,"C00029",cytosol,Day),
  in_compartment(Experiment,"C00668",cytosol,Day),
  catalyst(7630,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00052",cytosol,Day) :-
  not exclude(7641),
  Day >= 1,
  in_compartment(Experiment,"C00029",cytosol,Day),
  in_compartment(Experiment,"C03384",cytosol,Day),
  catalyst(7641,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00103",cytosol,Day) :-
  not exclude(7641),
  Day >= 1,
  in_compartment(Experiment,"C00029",cytosol,Day),
  in_compartment(Experiment,"C03384",cytosol,Day),
  catalyst(7641,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00029",cytosol,Day) :-
  not exclude(7642),
  Day >= 1,
  in_compartment(Experiment,"C00052",cytosol,Day),
  in_compartment(Experiment,"C00103",cytosol,Day),
  catalyst(7642,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03384",cytosol,Day) :-
  not exclude(7642),
  Day >= 1,
  in_compartment(Experiment,"C00052",cytosol,Day),
  in_compartment(Experiment,"C00103",cytosol,Day),
  catalyst(7642,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00124",cytosol,Day) :-
  not exclude(7650),
  Day >= 1,
  in_compartment(Experiment,"C05397",cytosol,Day),
  catalyst(7650,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00267",cytosol,Day) :-
  not exclude(7650),
  Day >= 1,
  in_compartment(Experiment,"C05397",cytosol,Day),
  catalyst(7650,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00267",cytosol,Day) :-
  not exclude(7660),
  Day >= 1,
  in_compartment(Experiment,"C00208",cytosol,Day),
  catalyst(7660,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00124",cytosol,Day) :-
  not exclude(7671),
  Day >= 1,
  in_compartment(Experiment,"C05399",cytosol,Day),
  catalyst(7671,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00794",cytosol,Day) :-
  not exclude(7671),
  Day >= 1,
  in_compartment(Experiment,"C05399",cytosol,Day),
  catalyst(7671,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05399",cytosol,Day) :-
  not exclude(7672),
  Day >= 1,
  in_compartment(Experiment,"C00124",cytosol,Day),
  in_compartment(Experiment,"C00794",cytosol,Day),
  catalyst(7672,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00116",cytosol,Day) :-
  not exclude(7681),
  Day >= 1,
  in_compartment(Experiment,"C05401",cytosol,Day),
  catalyst(7681,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00124",cytosol,Day) :-
  not exclude(7681),
  Day >= 1,
  in_compartment(Experiment,"C05401",cytosol,Day),
  catalyst(7681,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05401",cytosol,Day) :-
  not exclude(7682),
  Day >= 1,
  in_compartment(Experiment,"C00116",cytosol,Day),
  in_compartment(Experiment,"C00124",cytosol,Day),
  catalyst(7682,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00124",cytosol,Day) :-
  not exclude(7691),
  Day >= 1,
  in_compartment(Experiment,"C05400",cytosol,Day),
  catalyst(7691,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00936",cytosol,Day) :-
  not exclude(7691),
  Day >= 1,
  in_compartment(Experiment,"C05400",cytosol,Day),
  catalyst(7691,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05400",cytosol,Day) :-
  not exclude(7692),
  Day >= 1,
  in_compartment(Experiment,"C00124",cytosol,Day),
  in_compartment(Experiment,"C00936",cytosol,Day),
  catalyst(7692,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00124",cytosol,Day) :-
  not exclude(7701),
  Day >= 1,
  in_compartment(Experiment,"C01235",cytosol,Day),
  catalyst(7701,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00137",cytosol,Day) :-
  not exclude(7701),
  Day >= 1,
  in_compartment(Experiment,"C01235",cytosol,Day),
  catalyst(7701,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01235",cytosol,Day) :-
  not exclude(7702),
  Day >= 1,
  in_compartment(Experiment,"C00124",cytosol,Day),
  in_compartment(Experiment,"C00137",cytosol,Day),
  catalyst(7702,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00089",cytosol,Day) :-
  not exclude(7710),
  Day >= 1,
  in_compartment(Experiment,"C00492",cytosol,Day),
  catalyst(7710,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00124",cytosol,Day) :-
  not exclude(7710),
  Day >= 1,
  in_compartment(Experiment,"C00492",cytosol,Day),
  catalyst(7710,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00124",cytosol,Day) :-
  not exclude(7720),
  Day >= 1,
  in_compartment(Experiment,"C02472",cytosol,Day),
  catalyst(7720,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00267",cytosol,Day) :-
  not exclude(7720),
  Day >= 1,
  in_compartment(Experiment,"C02472",cytosol,Day),
  catalyst(7720,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00124",cytosol,Day) :-
  not exclude(7730),
  Day >= 1,
  in_compartment(Experiment,"C05402",cytosol,Day),
  catalyst(7730,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00267",cytosol,Day) :-
  not exclude(7730),
  Day >= 1,
  in_compartment(Experiment,"C05402",cytosol,Day),
  catalyst(7730,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(7741),
  Day >= 1,
  in_compartment(Experiment,"C00075",cytosol,Day),
  in_compartment(Experiment,"C00103",cytosol,Day),
  catalyst(7741,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00029",cytosol,Day) :-
  not exclude(7741),
  Day >= 1,
  in_compartment(Experiment,"C00075",cytosol,Day),
  in_compartment(Experiment,"C00103",cytosol,Day),
  catalyst(7741,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00075",cytosol,Day) :-
  not exclude(7742),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00029",cytosol,Day),
  catalyst(7742,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00103",cytosol,Day) :-
  not exclude(7742),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00029",cytosol,Day),
  catalyst(7742,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00029",cytosol,Day) :-
  not exclude(7751),
  Day >= 1,
  in_compartment(Experiment,"C00052",cytosol,Day),
  catalyst(7751,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00052",cytosol,Day) :-
  not exclude(7752),
  Day >= 1,
  in_compartment(Experiment,"C00029",cytosol,Day),
  catalyst(7752,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(7761),
  Day >= 1,
  in_compartment(Experiment,"C00075",cytosol,Day),
  in_compartment(Experiment,"C03384",cytosol,Day),
  catalyst(7761,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00052",cytosol,Day) :-
  not exclude(7761),
  Day >= 1,
  in_compartment(Experiment,"C00075",cytosol,Day),
  in_compartment(Experiment,"C03384",cytosol,Day),
  catalyst(7761,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00075",cytosol,Day) :-
  not exclude(7762),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00052",cytosol,Day),
  catalyst(7762,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03384",cytosol,Day) :-
  not exclude(7762),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00052",cytosol,Day),
  catalyst(7762,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(7770),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00124",cytosol,Day),
  catalyst(7770,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03384",cytosol,Day) :-
  not exclude(7770),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00124",cytosol,Day),
  catalyst(7770,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(7780),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00794",cytosol,Day),
  catalyst(7780,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00095",cytosol,Day) :-
  not exclude(7780),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00794",cytosol,Day),
  catalyst(7780,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(7790),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01094",cytosol,Day),
  catalyst(7790,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05378",cytosol,Day) :-
  not exclude(7790),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01094",cytosol,Day),
  catalyst(7790,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(7800),
  Day >= 1,
  in_compartment(Experiment,"C00665",cytosol,Day),
  catalyst(7800,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05345",cytosol,Day) :-
  not exclude(7800),
  Day >= 1,
  in_compartment(Experiment,"C00665",cytosol,Day),
  catalyst(7800,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(7820),
  Day >= 1,
  in_compartment(Experiment,"C00044",cytosol,Day),
  in_compartment(Experiment,"C03812",cytosol,Day),
  catalyst(7820,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00096",cytosol,Day) :-
  not exclude(7820),
  Day >= 1,
  in_compartment(Experiment,"C00044",cytosol,Day),
  in_compartment(Experiment,"C03812",cytosol,Day),
  catalyst(7820,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05345",cytosol,Day) :-
  not exclude(7841),
  Day >= 1,
  in_compartment(Experiment,"C00275",cytosol,Day),
  catalyst(7841,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00275",cytosol,Day) :-
  not exclude(7842),
  Day >= 1,
  in_compartment(Experiment,"C05345",cytosol,Day),
  catalyst(7842,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00117",cytosol,Day) :-
  not exclude(7861),
  Day >= 1,
  in_compartment(Experiment,"C00620",cytosol,Day),
  catalyst(7861,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00620",cytosol,Day) :-
  not exclude(7862),
  Day >= 1,
  in_compartment(Experiment,"C00117",cytosol,Day),
  catalyst(7862,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(7870),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01801",cytosol,Day),
  catalyst(7870,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00673",cytosol,Day) :-
  not exclude(7870),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01801",cytosol,Day),
  catalyst(7870,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(7880),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00121",cytosol,Day),
  catalyst(7880,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00117",cytosol,Day) :-
  not exclude(7880),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00121",cytosol,Day),
  catalyst(7880,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00279",cytosol,Day) :-
  not exclude(7891),
  Day >= 1,
  in_compartment(Experiment,"C00118",cytosol,Day),
  in_compartment(Experiment,"C00281",cytosol,Day),
  catalyst(7891,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05345",cytosol,Day) :-
  not exclude(7891),
  Day >= 1,
  in_compartment(Experiment,"C00118",cytosol,Day),
  in_compartment(Experiment,"C00281",cytosol,Day),
  catalyst(7891,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00118",cytosol,Day) :-
  not exclude(7892),
  Day >= 1,
  in_compartment(Experiment,"C00279",cytosol,Day),
  in_compartment(Experiment,"C05345",cytosol,Day),
  catalyst(7892,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00281",cytosol,Day) :-
  not exclude(7892),
  Day >= 1,
  in_compartment(Experiment,"C00279",cytosol,Day),
  in_compartment(Experiment,"C05345",cytosol,Day),
  catalyst(7892,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00118",cytosol,Day) :-
  not exclude(7901),
  Day >= 1,
  in_compartment(Experiment,"C00279",cytosol,Day),
  in_compartment(Experiment,"C06814",cytosol,Day),
  catalyst(7901,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05345",cytosol,Day) :-
  not exclude(7901),
  Day >= 1,
  in_compartment(Experiment,"C00279",cytosol,Day),
  in_compartment(Experiment,"C06814",cytosol,Day),
  catalyst(7901,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00279",cytosol,Day) :-
  not exclude(7902),
  Day >= 1,
  in_compartment(Experiment,"C00118",cytosol,Day),
  in_compartment(Experiment,"C05345",cytosol,Day),
  catalyst(7902,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C06814",cytosol,Day) :-
  not exclude(7902),
  Day >= 1,
  in_compartment(Experiment,"C00118",cytosol,Day),
  in_compartment(Experiment,"C05345",cytosol,Day),
  catalyst(7902,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00117",cytosol,Day) :-
  not exclude(7921),
  Day >= 1,
  in_compartment(Experiment,"C00199",cytosol,Day),
  catalyst(7921,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00199",cytosol,Day) :-
  not exclude(7922),
  Day >= 1,
  in_compartment(Experiment,"C00117",cytosol,Day),
  catalyst(7922,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C06814",cytosol,Day) :-
  not exclude(7931),
  Day >= 1,
  in_compartment(Experiment,"C00199",cytosol,Day),
  catalyst(7931,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00199",cytosol,Day) :-
  not exclude(7932),
  Day >= 1,
  in_compartment(Experiment,"C06814",cytosol,Day),
  catalyst(7932,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(7940),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00345",cytosol,Day),
  catalyst(7940,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(7940),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00345",cytosol,Day),
  catalyst(7940,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00199",cytosol,Day) :-
  not exclude(7940),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00345",cytosol,Day),
  catalyst(7940,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00345",cytosol,Day) :-
  not exclude(7950),
  Day >= 1,
  in_compartment(Experiment,"C01236",cytosol,Day),
  catalyst(7950,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(7961),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00668",cytosol,Day),
  catalyst(7961,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01236",cytosol,Day) :-
  not exclude(7961),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00668",cytosol,Day),
  catalyst(7961,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(7962),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C01236",cytosol,Day),
  catalyst(7962,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00668",cytosol,Day) :-
  not exclude(7962),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C01236",cytosol,Day),
  catalyst(7962,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(7980),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(7980,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(7980),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(7980,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00036",cytosol,Day) :-
  not exclude(7980),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(7980,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(7990),
  Day >= 1,
  in_compartment(Experiment,"C05378",cytosol,Day),
  catalyst(7990,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05345",cytosol,Day) :-
  not exclude(7990),
  Day >= 1,
  in_compartment(Experiment,"C05378",cytosol,Day),
  catalyst(7990,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(8000),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00036",cytosol,Day),
  catalyst(8000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(8000),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00036",cytosol,Day),
  catalyst(8000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00074",cytosol,Day) :-
  not exclude(8000),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00036",cytosol,Day),
  catalyst(8000,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(8010),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00048",cytosol,Day),
  catalyst(8010,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00711",cytosol,Day) :-
  not exclude(8010),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00048",cytosol,Day),
  catalyst(8010,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",cytosol,Day) :-
  not exclude(8020),
  Day >= 1,
  in_compartment(Experiment,"C00311",cytosol,Day),
  catalyst(8020,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00048",cytosol,Day) :-
  not exclude(8020),
  Day >= 1,
  in_compartment(Experiment,"C00311",cytosol,Day),
  catalyst(8020,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",mitochondrion,Day) :-
  not exclude(8041),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00711",mitochondrion,Day),
  catalyst(8041,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00036",mitochondrion,Day) :-
  not exclude(8041),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00711",mitochondrion,Day),
  catalyst(8041,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",mitochondrion,Day) :-
  not exclude(8042),
  Day >= 1,
  in_compartment(Experiment,"C00004",mitochondrion,Day),
  in_compartment(Experiment,"C00036",mitochondrion,Day),
  catalyst(8042,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00711",mitochondrion,Day) :-
  not exclude(8042),
  Day >= 1,
  in_compartment(Experiment,"C00004",mitochondrion,Day),
  in_compartment(Experiment,"C00036",mitochondrion,Day),
  catalyst(8042,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00711",mitochondrion,Day) :-
  not exclude(8061),
  Day >= 1,
  in_compartment(Experiment,"C00122",mitochondrion,Day),
  catalyst(8061,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00122",mitochondrion,Day) :-
  not exclude(8062),
  Day >= 1,
  in_compartment(Experiment,"C00711",mitochondrion,Day),
  catalyst(8062,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00016",mitochondrion,Day) :-
  not exclude(8070),
  Day >= 1,
  in_compartment(Experiment,"C00122",mitochondrion,Day),
  in_compartment(Experiment,"C01352",mitochondrion,Day),
  catalyst(8070,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",mitochondrion,Day) :-
  not exclude(8070),
  Day >= 1,
  in_compartment(Experiment,"C00122",mitochondrion,Day),
  in_compartment(Experiment,"C01352",mitochondrion,Day),
  catalyst(8070,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00016",mitochondrion,Day) :-
  not exclude(8080),
  Day >= 1,
  in_compartment(Experiment,"C00122",cytosol,Day),
  in_compartment(Experiment,"C01352",mitochondrion,Day),
  catalyst(8080,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",cytosol,Day) :-
  not exclude(8080),
  Day >= 1,
  in_compartment(Experiment,"C00122",cytosol,Day),
  in_compartment(Experiment,"C01352",mitochondrion,Day),
  catalyst(8080,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00122",mitochondrion,Day) :-
  not exclude(8091),
  Day >= 1,
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C00042",mitochondrion,Day),
  catalyst(8091,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01352",mitochondrion,Day) :-
  not exclude(8091),
  Day >= 1,
  in_compartment(Experiment,"C00016",mitochondrion,Day),
  in_compartment(Experiment,"C00042",mitochondrion,Day),
  catalyst(8091,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00016",mitochondrion,Day) :-
  not exclude(8092),
  Day >= 1,
  in_compartment(Experiment,"C00122",mitochondrion,Day),
  in_compartment(Experiment,"C01352",mitochondrion,Day),
  catalyst(8092,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",mitochondrion,Day) :-
  not exclude(8092),
  Day >= 1,
  in_compartment(Experiment,"C00122",mitochondrion,Day),
  in_compartment(Experiment,"C01352",mitochondrion,Day),
  catalyst(8092,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",mitochondrion,Day) :-
  not exclude(8111),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00010",mitochondrion,Day),
  in_compartment(Experiment,"C00042",mitochondrion,Day),
  catalyst(8111,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",mitochondrion,Day) :-
  not exclude(8111),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00010",mitochondrion,Day),
  in_compartment(Experiment,"C00042",mitochondrion,Day),
  catalyst(8111,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00091",mitochondrion,Day) :-
  not exclude(8111),
  Day >= 1,
  in_compartment(Experiment,"C00002",mitochondrion,Day),
  in_compartment(Experiment,"C00010",mitochondrion,Day),
  in_compartment(Experiment,"C00042",mitochondrion,Day),
  catalyst(8111,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",mitochondrion,Day) :-
  not exclude(8112),
  Day >= 1,
  in_compartment(Experiment,"C00008",mitochondrion,Day),
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  in_compartment(Experiment,"C00091",mitochondrion,Day),
  catalyst(8112,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",mitochondrion,Day) :-
  not exclude(8112),
  Day >= 1,
  in_compartment(Experiment,"C00008",mitochondrion,Day),
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  in_compartment(Experiment,"C00091",mitochondrion,Day),
  catalyst(8112,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",mitochondrion,Day) :-
  not exclude(8112),
  Day >= 1,
  in_compartment(Experiment,"C00008",mitochondrion,Day),
  in_compartment(Experiment,"C00009",mitochondrion,Day),
  in_compartment(Experiment,"C00091",mitochondrion,Day),
  catalyst(8112,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",mitochondrion,Day) :-
  not exclude(8120),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00010",mitochondrion,Day),
  in_compartment(Experiment,"C00026",mitochondrion,Day),
  catalyst(8120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(8120),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00010",mitochondrion,Day),
  in_compartment(Experiment,"C00026",mitochondrion,Day),
  catalyst(8120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00091",mitochondrion,Day) :-
  not exclude(8120),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00010",mitochondrion,Day),
  in_compartment(Experiment,"C00026",mitochondrion,Day),
  catalyst(8120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(8130),
  Day >= 1,
  in_compartment(Experiment,"C05379",cytosol,Day),
  catalyst(8130,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(8130),
  Day >= 1,
  in_compartment(Experiment,"C05379",cytosol,Day),
  catalyst(8130,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(8150),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00311",cytosol,Day),
  catalyst(8150,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05379",cytosol,Day) :-
  not exclude(8150),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00311",cytosol,Day),
  catalyst(8150,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",mitochondrion,Day) :-
  not exclude(8160),
  Day >= 1,
  in_compartment(Experiment,"C00006",mitochondrion,Day),
  in_compartment(Experiment,"C00311",mitochondrion,Day),
  catalyst(8160,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05379",mitochondrion,Day) :-
  not exclude(8160),
  Day >= 1,
  in_compartment(Experiment,"C00006",mitochondrion,Day),
  in_compartment(Experiment,"C00311",mitochondrion,Day),
  catalyst(8160,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00311",mitochondrion,Day) :-
  not exclude(8181),
  Day >= 1,
  in_compartment(Experiment,"C00158",mitochondrion,Day),
  catalyst(8181,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00158",mitochondrion,Day) :-
  not exclude(8182),
  Day >= 1,
  in_compartment(Experiment,"C00311",mitochondrion,Day),
  catalyst(8182,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",mitochondrion,Day) :-
  not exclude(8190),
  Day >= 1,
  in_compartment(Experiment,"C00024",mitochondrion,Day),
  in_compartment(Experiment,"C00036",mitochondrion,Day),
  catalyst(8190,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00158",mitochondrion,Day) :-
  not exclude(8190),
  Day >= 1,
  in_compartment(Experiment,"C00024",mitochondrion,Day),
  in_compartment(Experiment,"C00036",mitochondrion,Day),
  catalyst(8190,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(8200),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00036",cytosol,Day),
  catalyst(8200,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00158",cytosol,Day) :-
  not exclude(8200),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00036",cytosol,Day),
  catalyst(8200,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",mitochondrion,Day) :-
  not exclude(8210),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00010",mitochondrion,Day),
  in_compartment(Experiment,"C00022",mitochondrion,Day),
  catalyst(8210,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",mitochondrion,Day) :-
  not exclude(8210),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00010",mitochondrion,Day),
  in_compartment(Experiment,"C00022",mitochondrion,Day),
  catalyst(8210,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00024",mitochondrion,Day) :-
  not exclude(8210),
  Day >= 1,
  in_compartment(Experiment,"C00003",mitochondrion,Day),
  in_compartment(Experiment,"C00010",mitochondrion,Day),
  in_compartment(Experiment,"C00022",mitochondrion,Day),
  catalyst(8210,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00074",cytosol,Day) :-
  not exclude(8231),
  Day >= 1,
  in_compartment(Experiment,"C00631",cytosol,Day),
  catalyst(8231,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00631",cytosol,Day) :-
  not exclude(8232),
  Day >= 1,
  in_compartment(Experiment,"C00074",cytosol,Day),
  catalyst(8232,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00631",cytosol,Day) :-
  not exclude(8241),
  Day >= 1,
  in_compartment(Experiment,"C00197",cytosol,Day),
  catalyst(8241,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00197",cytosol,Day) :-
  not exclude(8242),
  Day >= 1,
  in_compartment(Experiment,"C00631",cytosol,Day),
  catalyst(8242,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01159",cytosol,Day) :-
  not exclude(8251),
  Day >= 1,
  in_compartment(Experiment,"C00236",cytosol,Day),
  catalyst(8251,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00236",cytosol,Day) :-
  not exclude(8252),
  Day >= 1,
  in_compartment(Experiment,"C01159",cytosol,Day),
  catalyst(8252,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8261),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00236",cytosol,Day),
  catalyst(8261,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00197",cytosol,Day) :-
  not exclude(8261),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00236",cytosol,Day),
  catalyst(8261,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(8262),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00197",cytosol,Day),
  catalyst(8262,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00236",cytosol,Day) :-
  not exclude(8262),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00197",cytosol,Day),
  catalyst(8262,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(8271),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00118",cytosol,Day),
  catalyst(8271,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00236",cytosol,Day) :-
  not exclude(8271),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00118",cytosol,Day),
  catalyst(8271,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(8272),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00236",cytosol,Day),
  catalyst(8272,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(8272),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00236",cytosol,Day),
  catalyst(8272,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00118",cytosol,Day) :-
  not exclude(8272),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00236",cytosol,Day),
  catalyst(8272,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00118",cytosol,Day) :-
  not exclude(8281),
  Day >= 1,
  in_compartment(Experiment,"C00111",cytosol,Day),
  catalyst(8281,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00111",cytosol,Day) :-
  not exclude(8282),
  Day >= 1,
  in_compartment(Experiment,"C00118",cytosol,Day),
  catalyst(8282,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(8300),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00281",cytosol,Day),
  catalyst(8300,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00447",cytosol,Day) :-
  not exclude(8300),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00281",cytosol,Day),
  catalyst(8300,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(8320),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C05345",cytosol,Day),
  catalyst(8320,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05378",cytosol,Day) :-
  not exclude(8320),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C05345",cytosol,Day),
  catalyst(8320,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01172",cytosol,Day) :-
  not exclude(8341),
  Day >= 1,
  in_compartment(Experiment,"C00668",cytosol,Day),
  catalyst(8341,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00668",cytosol,Day) :-
  not exclude(8342),
  Day >= 1,
  in_compartment(Experiment,"C01172",cytosol,Day),
  catalyst(8342,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05345",cytosol,Day) :-
  not exclude(8351),
  Day >= 1,
  in_compartment(Experiment,"C00668",cytosol,Day),
  catalyst(8351,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00668",cytosol,Day) :-
  not exclude(8352),
  Day >= 1,
  in_compartment(Experiment,"C05345",cytosol,Day),
  catalyst(8352,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(8360),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00095",cytosol,Day),
  catalyst(8360,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05345",cytosol,Day) :-
  not exclude(8360),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00095",cytosol,Day),
  catalyst(8360,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(8370),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00936",cytosol,Day),
  catalyst(8370,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00275",cytosol,Day) :-
  not exclude(8370),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00936",cytosol,Day),
  catalyst(8370,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(8390),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00221",cytosol,Day),
  catalyst(8390,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00668",cytosol,Day) :-
  not exclude(8390),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00221",cytosol,Day),
  catalyst(8390,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(8400),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00221",cytosol,Day),
  catalyst(8400,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01172",cytosol,Day) :-
  not exclude(8400),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00221",cytosol,Day),
  catalyst(8400,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8411),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C03638",cytosol,Day),
  catalyst(8411,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8411),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C03638",cytosol,Day),
  catalyst(8411,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04312",cytosol,Day) :-
  not exclude(8411),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C03638",cytosol,Day),
  catalyst(8411,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8412),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C04312",cytosol,Day),
  catalyst(8412,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03638",cytosol,Day) :-
  not exclude(8412),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C04312",cytosol,Day),
  catalyst(8412,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8421),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00046",cytosol,Day),
  catalyst(8421,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8421),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00046",cytosol,Day),
  catalyst(8421,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02073",cytosol,Day) :-
  not exclude(8421),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00046",cytosol,Day),
  catalyst(8421,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8422),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02073",cytosol,Day),
  catalyst(8422,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00046",cytosol,Day) :-
  not exclude(8422),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02073",cytosol,Day),
  catalyst(8422,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8431),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00039",cytosol,Day),
  catalyst(8431,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8431),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00039",cytosol,Day),
  catalyst(8431,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00039",cytosol,Day) :-
  not exclude(8431),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00039",cytosol,Day),
  catalyst(8431,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8432),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C00039",cytosol,Day),
  catalyst(8432,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00039",cytosol,Day) :-
  not exclude(8432),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C00039",cytosol,Day),
  catalyst(8432,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8441),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00120",cytosol,Day),
  in_compartment(Experiment,"C04735",cytosol,Day),
  catalyst(8441,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8441),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00120",cytosol,Day),
  in_compartment(Experiment,"C04735",cytosol,Day),
  catalyst(8441,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04681",cytosol,Day) :-
  not exclude(8441),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00120",cytosol,Day),
  in_compartment(Experiment,"C04735",cytosol,Day),
  catalyst(8441,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8442),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C04681",cytosol,Day),
  catalyst(8442,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00120",cytosol,Day) :-
  not exclude(8442),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C04681",cytosol,Day),
  catalyst(8442,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04735",cytosol,Day) :-
  not exclude(8442),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C04681",cytosol,Day),
  catalyst(8442,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8451),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00120",cytosol,Day),
  in_compartment(Experiment,"C04827",cytosol,Day),
  catalyst(8451,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8451),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00120",cytosol,Day),
  in_compartment(Experiment,"C04827",cytosol,Day),
  catalyst(8451,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04801",cytosol,Day) :-
  not exclude(8451),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00120",cytosol,Day),
  in_compartment(Experiment,"C04827",cytosol,Day),
  catalyst(8451,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8452),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C04801",cytosol,Day),
  catalyst(8452,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00120",cytosol,Day) :-
  not exclude(8452),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C04801",cytosol,Day),
  catalyst(8452,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04827",cytosol,Day) :-
  not exclude(8452),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C04801",cytosol,Day),
  catalyst(8452,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8461),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00120",cytosol,Day),
  in_compartment(Experiment,"C04763",cytosol,Day),
  catalyst(8461,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8461),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00120",cytosol,Day),
  in_compartment(Experiment,"C04763",cytosol,Day),
  catalyst(8461,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04727",cytosol,Day) :-
  not exclude(8461),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00120",cytosol,Day),
  in_compartment(Experiment,"C04763",cytosol,Day),
  catalyst(8461,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8462),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C04727",cytosol,Day),
  catalyst(8462,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00120",cytosol,Day) :-
  not exclude(8462),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C04727",cytosol,Day),
  catalyst(8462,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04763",cytosol,Day) :-
  not exclude(8462),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C04727",cytosol,Day),
  catalyst(8462,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8481),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00120",cytosol,Day),
  in_compartment(Experiment,"C04736",cytosol,Day),
  catalyst(8481,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8481),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00120",cytosol,Day),
  in_compartment(Experiment,"C04736",cytosol,Day),
  catalyst(8481,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04682",cytosol,Day) :-
  not exclude(8481),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00120",cytosol,Day),
  in_compartment(Experiment,"C04736",cytosol,Day),
  catalyst(8481,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8482),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C04682",cytosol,Day),
  catalyst(8482,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00120",cytosol,Day) :-
  not exclude(8482),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C04682",cytosol,Day),
  catalyst(8482,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04736",cytosol,Day) :-
  not exclude(8482),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C04682",cytosol,Day),
  catalyst(8482,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(8491),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C03479",cytosol,Day),
  catalyst(8491,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(8491),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C03479",cytosol,Day),
  catalyst(8491,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00445",cytosol,Day) :-
  not exclude(8491),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C03479",cytosol,Day),
  catalyst(8491,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8492),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00445",cytosol,Day),
  catalyst(8492,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03479",cytosol,Day) :-
  not exclude(8492),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00445",cytosol,Day),
  catalyst(8492,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8511),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00152",cytosol,Day),
  in_compartment(Experiment,"C01637",cytosol,Day),
  catalyst(8511,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8511),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00152",cytosol,Day),
  in_compartment(Experiment,"C01637",cytosol,Day),
  catalyst(8511,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03402",cytosol,Day) :-
  not exclude(8511),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00152",cytosol,Day),
  in_compartment(Experiment,"C01637",cytosol,Day),
  catalyst(8511,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8512),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03402",cytosol,Day),
  catalyst(8512,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00152",cytosol,Day) :-
  not exclude(8512),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03402",cytosol,Day),
  catalyst(8512,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01637",cytosol,Day) :-
  not exclude(8512),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03402",cytosol,Day),
  catalyst(8512,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8521),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00079",cytosol,Day),
  in_compartment(Experiment,"C01648",cytosol,Day),
  catalyst(8521,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8521),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00079",cytosol,Day),
  in_compartment(Experiment,"C01648",cytosol,Day),
  catalyst(8521,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03511",cytosol,Day) :-
  not exclude(8521),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00079",cytosol,Day),
  in_compartment(Experiment,"C01648",cytosol,Day),
  catalyst(8521,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8522),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03511",cytosol,Day),
  catalyst(8522,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00079",cytosol,Day) :-
  not exclude(8522),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03511",cytosol,Day),
  catalyst(8522,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01648",cytosol,Day) :-
  not exclude(8522),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03511",cytosol,Day),
  catalyst(8522,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8531),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C01640",cytosol,Day),
  catalyst(8531,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8531),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C01640",cytosol,Day),
  catalyst(8531,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02282",cytosol,Day) :-
  not exclude(8531),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C01640",cytosol,Day),
  catalyst(8531,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8532),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02282",cytosol,Day),
  catalyst(8532,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00064",cytosol,Day) :-
  not exclude(8532),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02282",cytosol,Day),
  catalyst(8532,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01640",cytosol,Day) :-
  not exclude(8532),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02282",cytosol,Day),
  catalyst(8532,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8551),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00148",cytosol,Day),
  in_compartment(Experiment,"C01649",cytosol,Day),
  catalyst(8551,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8551),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00148",cytosol,Day),
  in_compartment(Experiment,"C01649",cytosol,Day),
  catalyst(8551,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02702",cytosol,Day) :-
  not exclude(8551),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00148",cytosol,Day),
  in_compartment(Experiment,"C01649",cytosol,Day),
  catalyst(8551,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8552),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02702",cytosol,Day),
  catalyst(8552,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00148",cytosol,Day) :-
  not exclude(8552),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02702",cytosol,Day),
  catalyst(8552,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01649",cytosol,Day) :-
  not exclude(8552),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02702",cytosol,Day),
  catalyst(8552,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8561),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00037",cytosol,Day),
  in_compartment(Experiment,"C01642",cytosol,Day),
  catalyst(8561,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8561),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00037",cytosol,Day),
  in_compartment(Experiment,"C01642",cytosol,Day),
  catalyst(8561,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02412",cytosol,Day) :-
  not exclude(8561),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00037",cytosol,Day),
  in_compartment(Experiment,"C01642",cytosol,Day),
  catalyst(8561,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8562),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02412",cytosol,Day),
  catalyst(8562,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00037",cytosol,Day) :-
  not exclude(8562),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02412",cytosol,Day),
  catalyst(8562,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01642",cytosol,Day) :-
  not exclude(8562),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02412",cytosol,Day),
  catalyst(8562,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8571),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C01638",cytosol,Day),
  catalyst(8571,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8571),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C01638",cytosol,Day),
  catalyst(8571,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02984",cytosol,Day) :-
  not exclude(8571),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C01638",cytosol,Day),
  catalyst(8571,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8572),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02984",cytosol,Day),
  catalyst(8572,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00049",cytosol,Day) :-
  not exclude(8572),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02984",cytosol,Day),
  catalyst(8572,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01638",cytosol,Day) :-
  not exclude(8572),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02984",cytosol,Day),
  catalyst(8572,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8581),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C01637",cytosol,Day),
  catalyst(8581,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8581),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C01637",cytosol,Day),
  catalyst(8581,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C06113",cytosol,Day) :-
  not exclude(8581),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00049",cytosol,Day),
  in_compartment(Experiment,"C01637",cytosol,Day),
  catalyst(8581,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8582),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C06113",cytosol,Day),
  catalyst(8582,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00049",cytosol,Day) :-
  not exclude(8582),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C06113",cytosol,Day),
  catalyst(8582,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01637",cytosol,Day) :-
  not exclude(8582),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C06113",cytosol,Day),
  catalyst(8582,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8591),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00065",cytosol,Day),
  in_compartment(Experiment,"C01650",cytosol,Day),
  catalyst(8591,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8591),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00065",cytosol,Day),
  in_compartment(Experiment,"C01650",cytosol,Day),
  catalyst(8591,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02553",cytosol,Day) :-
  not exclude(8591),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00065",cytosol,Day),
  in_compartment(Experiment,"C01650",cytosol,Day),
  catalyst(8591,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8592),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02553",cytosol,Day),
  catalyst(8592,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00065",cytosol,Day) :-
  not exclude(8592),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02553",cytosol,Day),
  catalyst(8592,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01650",cytosol,Day) :-
  not exclude(8592),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02553",cytosol,Day),
  catalyst(8592,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8601),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01647",cytosol,Day),
  in_compartment(Experiment,"C05335",cytosol,Day),
  catalyst(8601,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8601),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01647",cytosol,Day),
  in_compartment(Experiment,"C05335",cytosol,Day),
  catalyst(8601,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05336",cytosol,Day) :-
  not exclude(8601),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01647",cytosol,Day),
  in_compartment(Experiment,"C05335",cytosol,Day),
  catalyst(8601,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8602),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C05336",cytosol,Day),
  catalyst(8602,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01647",cytosol,Day) :-
  not exclude(8602),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C05336",cytosol,Day),
  catalyst(8602,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05335",cytosol,Day) :-
  not exclude(8602),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C05336",cytosol,Day),
  catalyst(8602,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8611),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00073",cytosol,Day),
  in_compartment(Experiment,"C01647",cytosol,Day),
  catalyst(8611,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8611),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00073",cytosol,Day),
  in_compartment(Experiment,"C01647",cytosol,Day),
  catalyst(8611,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02430",cytosol,Day) :-
  not exclude(8611),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00073",cytosol,Day),
  in_compartment(Experiment,"C01647",cytosol,Day),
  catalyst(8611,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8612),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02430",cytosol,Day),
  catalyst(8612,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00073",cytosol,Day) :-
  not exclude(8612),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02430",cytosol,Day),
  catalyst(8612,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01647",cytosol,Day) :-
  not exclude(8612),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02430",cytosol,Day),
  catalyst(8612,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8621),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00183",cytosol,Day),
  in_compartment(Experiment,"C01653",cytosol,Day),
  catalyst(8621,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8621),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00183",cytosol,Day),
  in_compartment(Experiment,"C01653",cytosol,Day),
  catalyst(8621,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02554",cytosol,Day) :-
  not exclude(8621),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00183",cytosol,Day),
  in_compartment(Experiment,"C01653",cytosol,Day),
  catalyst(8621,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8622),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02554",cytosol,Day),
  catalyst(8622,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00183",cytosol,Day) :-
  not exclude(8622),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02554",cytosol,Day),
  catalyst(8622,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01653",cytosol,Day) :-
  not exclude(8622),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02554",cytosol,Day),
  catalyst(8622,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8631),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00041",cytosol,Day),
  in_compartment(Experiment,"C01635",cytosol,Day),
  catalyst(8631,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8631),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00041",cytosol,Day),
  in_compartment(Experiment,"C01635",cytosol,Day),
  catalyst(8631,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00886",cytosol,Day) :-
  not exclude(8631),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00041",cytosol,Day),
  in_compartment(Experiment,"C01635",cytosol,Day),
  catalyst(8631,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8632),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C00886",cytosol,Day),
  catalyst(8632,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00041",cytosol,Day) :-
  not exclude(8632),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C00886",cytosol,Day),
  catalyst(8632,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01635",cytosol,Day) :-
  not exclude(8632),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C00886",cytosol,Day),
  catalyst(8632,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8641),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00407",cytosol,Day),
  in_compartment(Experiment,"C01644",cytosol,Day),
  catalyst(8641,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8641),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00407",cytosol,Day),
  in_compartment(Experiment,"C01644",cytosol,Day),
  catalyst(8641,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03127",cytosol,Day) :-
  not exclude(8641),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00407",cytosol,Day),
  in_compartment(Experiment,"C01644",cytosol,Day),
  catalyst(8641,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8642),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03127",cytosol,Day),
  catalyst(8642,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00407",cytosol,Day) :-
  not exclude(8642),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03127",cytosol,Day),
  catalyst(8642,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01644",cytosol,Day) :-
  not exclude(8642),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03127",cytosol,Day),
  catalyst(8642,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8651),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00123",cytosol,Day),
  in_compartment(Experiment,"C01645",cytosol,Day),
  catalyst(8651,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8651),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00123",cytosol,Day),
  in_compartment(Experiment,"C01645",cytosol,Day),
  catalyst(8651,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02047",cytosol,Day) :-
  not exclude(8651),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00123",cytosol,Day),
  in_compartment(Experiment,"C01645",cytosol,Day),
  catalyst(8651,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8652),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02047",cytosol,Day),
  catalyst(8652,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00123",cytosol,Day) :-
  not exclude(8652),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02047",cytosol,Day),
  catalyst(8652,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01645",cytosol,Day) :-
  not exclude(8652),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02047",cytosol,Day),
  catalyst(8652,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8661),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00188",cytosol,Day),
  in_compartment(Experiment,"C01651",cytosol,Day),
  catalyst(8661,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8661),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00188",cytosol,Day),
  in_compartment(Experiment,"C01651",cytosol,Day),
  catalyst(8661,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02992",cytosol,Day) :-
  not exclude(8661),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00188",cytosol,Day),
  in_compartment(Experiment,"C01651",cytosol,Day),
  catalyst(8661,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8662),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02992",cytosol,Day),
  catalyst(8662,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00188",cytosol,Day) :-
  not exclude(8662),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02992",cytosol,Day),
  catalyst(8662,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01651",cytosol,Day) :-
  not exclude(8662),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C02992",cytosol,Day),
  catalyst(8662,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(8671),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00078",cytosol,Day),
  in_compartment(Experiment,"C01652",cytosol,Day),
  catalyst(8671,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8671),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00078",cytosol,Day),
  in_compartment(Experiment,"C01652",cytosol,Day),
  catalyst(8671,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03512",cytosol,Day) :-
  not exclude(8671),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00078",cytosol,Day),
  in_compartment(Experiment,"C01652",cytosol,Day),
  catalyst(8671,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8672),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03512",cytosol,Day),
  catalyst(8672,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00078",cytosol,Day) :-
  not exclude(8672),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03512",cytosol,Day),
  catalyst(8672,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01652",cytosol,Day) :-
  not exclude(8672),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C03512",cytosol,Day),
  catalyst(8672,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00221",cytosol,Day) :-
  not exclude(8711),
  Day >= 1,
  in_compartment(Experiment,"C00267",cytosol,Day),
  catalyst(8711,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00267",cytosol,Day) :-
  not exclude(8712),
  Day >= 1,
  in_compartment(Experiment,"C00221",cytosol,Day),
  catalyst(8712,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8741),
  Day >= 1,
  in_compartment(Experiment,"C00065",cytosol,Day),
  catalyst(8741,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02218",cytosol,Day) :-
  not exclude(8741),
  Day >= 1,
  in_compartment(Experiment,"C00065",cytosol,Day),
  catalyst(8741,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00065",cytosol,Day) :-
  not exclude(8742),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C02218",cytosol,Day),
  catalyst(8742,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(8751),
  Day >= 1,
  in_compartment(Experiment,"C00065",cytosol,Day),
  catalyst(8751,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(8751),
  Day >= 1,
  in_compartment(Experiment,"C00065",cytosol,Day),
  catalyst(8751,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00065",cytosol,Day) :-
  not exclude(8752),
  Day >= 1,
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(8752,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00346",cytosol,Day) :-
  not exclude(8781),
  Day >= 1,
  in_compartment(Experiment,"C01120",cytosol,Day),
  catalyst(8781,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00517",cytosol,Day) :-
  not exclude(8781),
  Day >= 1,
  in_compartment(Experiment,"C01120",cytosol,Day),
  catalyst(8781,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01120",cytosol,Day) :-
  not exclude(8782),
  Day >= 1,
  in_compartment(Experiment,"C00346",cytosol,Day),
  in_compartment(Experiment,"C00517",cytosol,Day),
  catalyst(8782,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05125",cytosol,Day) :-
  not exclude(8791),
  Day >= 1,
  in_compartment(Experiment,"C00068",cytosol,Day),
  in_compartment(Experiment,"C00084",cytosol,Day),
  catalyst(8791,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00068",cytosol,Day) :-
  not exclude(8792),
  Day >= 1,
  in_compartment(Experiment,"C05125",cytosol,Day),
  catalyst(8792,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00084",cytosol,Day) :-
  not exclude(8792),
  Day >= 1,
  in_compartment(Experiment,"C05125",cytosol,Day),
  catalyst(8792,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(8801),
  Day >= 1,
  in_compartment(Experiment,"C00161",cytosol,Day),
  catalyst(8801,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00071",cytosol,Day) :-
  not exclude(8801),
  Day >= 1,
  in_compartment(Experiment,"C00161",cytosol,Day),
  catalyst(8801,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00161",cytosol,Day) :-
  not exclude(8802),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00071",cytosol,Day),
  catalyst(8802,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(8811),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(8811,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00084",cytosol,Day) :-
  not exclude(8811),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(8811,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(8812),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00084",cytosol,Day),
  catalyst(8812,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8821),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00301",cytosol,Day),
  catalyst(8821,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00117",cytosol,Day) :-
  not exclude(8821),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00301",cytosol,Day),
  catalyst(8821,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8822),
  Day >= 1,
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C00117",cytosol,Day),
  catalyst(8822,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00301",cytosol,Day) :-
  not exclude(8822),
  Day >= 1,
  in_compartment(Experiment,"C00020",cytosol,Day),
  in_compartment(Experiment,"C00117",cytosol,Day),
  catalyst(8822,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(8831),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C04494",cytosol,Day),
  catalyst(8831,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01228",cytosol,Day) :-
  not exclude(8831),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C04494",cytosol,Day),
  catalyst(8831,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8832),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C01228",cytosol,Day),
  catalyst(8832,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04494",cytosol,Day) :-
  not exclude(8832),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C01228",cytosol,Day),
  catalyst(8832,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(8841),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00890",cytosol,Day),
  catalyst(8841,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00890",cytosol,Day) :-
  not exclude(8841),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00890",cytosol,Day),
  catalyst(8841,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8842),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00890",cytosol,Day),
  catalyst(8842,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00890",cytosol,Day) :-
  not exclude(8842),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00890",cytosol,Day),
  catalyst(8842,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(8851),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00459",cytosol,Day),
  catalyst(8851,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00363",cytosol,Day) :-
  not exclude(8851),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00459",cytosol,Day),
  catalyst(8851,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8852),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00363",cytosol,Day),
  catalyst(8852,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00459",cytosol,Day) :-
  not exclude(8852),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00363",cytosol,Day),
  catalyst(8852,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(8861),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00363",cytosol,Day),
  catalyst(8861,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00364",cytosol,Day) :-
  not exclude(8861),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00363",cytosol,Day),
  catalyst(8861,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8862),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00364",cytosol,Day),
  catalyst(8862,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00363",cytosol,Day) :-
  not exclude(8862),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00364",cytosol,Day),
  catalyst(8862,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(8871),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00104",cytosol,Day),
  catalyst(8871,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00130",cytosol,Day) :-
  not exclude(8871),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00104",cytosol,Day),
  catalyst(8871,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8872),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00130",cytosol,Day),
  catalyst(8872,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00104",cytosol,Day) :-
  not exclude(8872),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00130",cytosol,Day),
  catalyst(8872,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(8881),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00081",cytosol,Day),
  catalyst(8881,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00104",cytosol,Day) :-
  not exclude(8881),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00081",cytosol,Day),
  catalyst(8881,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8882),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00104",cytosol,Day),
  catalyst(8882,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00081",cytosol,Day) :-
  not exclude(8882),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00104",cytosol,Day),
  catalyst(8882,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(8891),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00063",cytosol,Day),
  catalyst(8891,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00112",cytosol,Day) :-
  not exclude(8891),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00063",cytosol,Day),
  catalyst(8891,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8892),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00112",cytosol,Day),
  catalyst(8892,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00063",cytosol,Day) :-
  not exclude(8892),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00112",cytosol,Day),
  catalyst(8892,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(8901),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00112",cytosol,Day),
  catalyst(8901,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00055",cytosol,Day) :-
  not exclude(8901),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00112",cytosol,Day),
  catalyst(8901,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8902),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00055",cytosol,Day),
  catalyst(8902,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00112",cytosol,Day) :-
  not exclude(8902),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00055",cytosol,Day),
  catalyst(8902,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(8931),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00075",cytosol,Day),
  catalyst(8931,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00015",cytosol,Day) :-
  not exclude(8931),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00075",cytosol,Day),
  catalyst(8931,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8932),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00015",cytosol,Day),
  catalyst(8932,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00075",cytosol,Day) :-
  not exclude(8932),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00015",cytosol,Day),
  catalyst(8932,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(8941),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00015",cytosol,Day),
  catalyst(8941,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00105",cytosol,Day) :-
  not exclude(8941),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00015",cytosol,Day),
  catalyst(8941,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8942),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00105",cytosol,Day),
  catalyst(8942,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00015",cytosol,Day) :-
  not exclude(8942),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00105",cytosol,Day),
  catalyst(8942,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(8951),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00008",cytosol,Day),
  catalyst(8951,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8951),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00008",cytosol,Day),
  catalyst(8951,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8952),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  catalyst(8952,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(8952),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  catalyst(8952,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(8971),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00002",cytosol,Day),
  catalyst(8971,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00020",cytosol,Day) :-
  not exclude(8971),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00002",cytosol,Day),
  catalyst(8971,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8972),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  catalyst(8972,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(8972),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00020",cytosol,Day),
  catalyst(8972,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(8991),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00242",cytosol,Day),
  catalyst(8991,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00385",cytosol,Day) :-
  not exclude(8991),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00242",cytosol,Day),
  catalyst(8991,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(8992),
  Day >= 1,
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00385",cytosol,Day),
  catalyst(8992,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00242",cytosol,Day) :-
  not exclude(8992),
  Day >= 1,
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00385",cytosol,Day),
  catalyst(8992,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02165",cytosol,Day) :-
  not exclude(9021),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00909",cytosol,Day),
  catalyst(9021,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9022),
  Day >= 1,
  in_compartment(Experiment,"C02165",cytosol,Day),
  catalyst(9022,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00909",cytosol,Day) :-
  not exclude(9022),
  Day >= 1,
  in_compartment(Experiment,"C02165",cytosol,Day),
  catalyst(9022,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00267",cytosol,Day) :-
  not exclude(9041),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C05873",cytosol,Day),
  catalyst(9041,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05874",cytosol,Day) :-
  not exclude(9041),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C05873",cytosol,Day),
  catalyst(9041,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9042),
  Day >= 1,
  in_compartment(Experiment,"C00267",cytosol,Day),
  in_compartment(Experiment,"C05874",cytosol,Day),
  catalyst(9042,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05873",cytosol,Day) :-
  not exclude(9042),
  Day >= 1,
  in_compartment(Experiment,"C00267",cytosol,Day),
  in_compartment(Experiment,"C05874",cytosol,Day),
  catalyst(9042,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00470",cytosol,Day) :-
  not exclude(9051),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00470",cytosol,Day),
  catalyst(9051,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04733",cytosol,Day) :-
  not exclude(9051),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00470",cytosol,Day),
  catalyst(9051,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9052),
  Day >= 1,
  in_compartment(Experiment,"C00470",cytosol,Day),
  in_compartment(Experiment,"C04733",cytosol,Day),
  catalyst(9052,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00470",cytosol,Day) :-
  not exclude(9052),
  Day >= 1,
  in_compartment(Experiment,"C00470",cytosol,Day),
  in_compartment(Experiment,"C04733",cytosol,Day),
  catalyst(9052,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00333",cytosol,Day) :-
  not exclude(9061),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00470",cytosol,Day),
  catalyst(9061,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9062),
  Day >= 1,
  in_compartment(Experiment,"C00333",cytosol,Day),
  catalyst(9062,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00470",cytosol,Day) :-
  not exclude(9062),
  Day >= 1,
  in_compartment(Experiment,"C00333",cytosol,Day),
  catalyst(9062,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03518",cytosol,Day) :-
  not exclude(9071),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00461",cytosol,Day),
  catalyst(9071,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9072),
  Day >= 1,
  in_compartment(Experiment,"C03518",cytosol,Day),
  catalyst(9072,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00461",cytosol,Day) :-
  not exclude(9072),
  Day >= 1,
  in_compartment(Experiment,"C03518",cytosol,Day),
  catalyst(9072,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00140",cytosol,Day) :-
  not exclude(9081),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00461",cytosol,Day),
  catalyst(9081,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9082),
  Day >= 1,
  in_compartment(Experiment,"C00140",cytosol,Day),
  catalyst(9082,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00461",cytosol,Day) :-
  not exclude(9082),
  Day >= 1,
  in_compartment(Experiment,"C00140",cytosol,Day),
  catalyst(9082,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00189",cytosol,Day) :-
  not exclude(9131),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00350",cytosol,Day),
  catalyst(9131,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00416",cytosol,Day) :-
  not exclude(9131),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00350",cytosol,Day),
  catalyst(9131,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9132),
  Day >= 1,
  in_compartment(Experiment,"C00189",cytosol,Day),
  in_compartment(Experiment,"C00416",cytosol,Day),
  catalyst(9132,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00350",cytosol,Day) :-
  not exclude(9132),
  Day >= 1,
  in_compartment(Experiment,"C00189",cytosol,Day),
  in_compartment(Experiment,"C00416",cytosol,Day),
  catalyst(9132,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00114",cytosol,Day) :-
  not exclude(9141),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00157",cytosol,Day),
  catalyst(9141,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00416",cytosol,Day) :-
  not exclude(9141),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00157",cytosol,Day),
  catalyst(9141,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9142),
  Day >= 1,
  in_compartment(Experiment,"C00114",cytosol,Day),
  in_compartment(Experiment,"C00416",cytosol,Day),
  catalyst(9142,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00157",cytosol,Day) :-
  not exclude(9142),
  Day >= 1,
  in_compartment(Experiment,"C00114",cytosol,Day),
  in_compartment(Experiment,"C00416",cytosol,Day),
  catalyst(9142,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(9161),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00354",cytosol,Day),
  catalyst(9161,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01094",cytosol,Day) :-
  not exclude(9161),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00354",cytosol,Day),
  catalyst(9161,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9162),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C01094",cytosol,Day),
  catalyst(9162,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00354",cytosol,Day) :-
  not exclude(9162),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C01094",cytosol,Day),
  catalyst(9162,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(9181),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C03475",cytosol,Day),
  catalyst(9181,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00419",cytosol,Day) :-
  not exclude(9181),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C03475",cytosol,Day),
  catalyst(9181,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9182),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00419",cytosol,Day),
  catalyst(9182,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03475",cytosol,Day) :-
  not exclude(9182),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00419",cytosol,Day),
  catalyst(9182,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(9191),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00562",cytosol,Day),
  catalyst(9191,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00017",cytosol,Day) :-
  not exclude(9191),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00562",cytosol,Day),
  catalyst(9191,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9192),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00017",cytosol,Day),
  catalyst(9192,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00562",cytosol,Day) :-
  not exclude(9192),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00017",cytosol,Day),
  catalyst(9192,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(9201),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C03360",cytosol,Day),
  catalyst(9201,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00870",cytosol,Day) :-
  not exclude(9201),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C03360",cytosol,Day),
  catalyst(9201,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9202),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00870",cytosol,Day),
  catalyst(9202,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03360",cytosol,Day) :-
  not exclude(9202),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00870",cytosol,Day),
  catalyst(9202,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(9211),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C01153",cytosol,Day),
  catalyst(9211,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00069",cytosol,Day) :-
  not exclude(9211),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C01153",cytosol,Day),
  catalyst(9211,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9212),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00069",cytosol,Day),
  catalyst(9212,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01153",cytosol,Day) :-
  not exclude(9212),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00069",cytosol,Day),
  catalyst(9212,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(9221),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00061",cytosol,Day),
  catalyst(9221,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00255",cytosol,Day) :-
  not exclude(9221),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00061",cytosol,Day),
  catalyst(9221,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9222),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00255",cytosol,Day),
  catalyst(9222,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00061",cytosol,Day) :-
  not exclude(9222),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00255",cytosol,Day),
  catalyst(9222,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00145",cytosol,Day) :-
  not exclude(9231),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C04090",cytosol,Day),
  catalyst(9231,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00496",cytosol,Day) :-
  not exclude(9231),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C04090",cytosol,Day),
  catalyst(9231,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9232),
  Day >= 1,
  in_compartment(Experiment,"C00145",cytosol,Day),
  in_compartment(Experiment,"C00496",cytosol,Day),
  catalyst(9232,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04090",cytosol,Day) :-
  not exclude(9232),
  Day >= 1,
  in_compartment(Experiment,"C00145",cytosol,Day),
  in_compartment(Experiment,"C00496",cytosol,Day),
  catalyst(9232,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(9241),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00154",cytosol,Day),
  catalyst(9241,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00249",cytosol,Day) :-
  not exclude(9241),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00154",cytosol,Day),
  catalyst(9241,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9242),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00249",cytosol,Day),
  catalyst(9242,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00154",cytosol,Day) :-
  not exclude(9242),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00249",cytosol,Day),
  catalyst(9242,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C07091",cytosol,Day) :-
  not exclude(9261),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C07090",cytosol,Day),
  catalyst(9261,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9262),
  Day >= 1,
  in_compartment(Experiment,"C07091",cytosol,Day),
  catalyst(9262,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C07090",cytosol,Day) :-
  not exclude(9262),
  Day >= 1,
  in_compartment(Experiment,"C07091",cytosol,Day),
  catalyst(9262,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02222",cytosol,Day) :-
  not exclude(9271),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C04431",cytosol,Day),
  catalyst(9271,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9272),
  Day >= 1,
  in_compartment(Experiment,"C02222",cytosol,Day),
  catalyst(9272,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04431",cytosol,Day) :-
  not exclude(9272),
  Day >= 1,
  in_compartment(Experiment,"C02222",cytosol,Day),
  catalyst(9272,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00670",cytosol,Day) :-
  not exclude(9291),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C04517",cytosol,Day),
  catalyst(9291,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C06015",cytosol,Day) :-
  not exclude(9291),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C04517",cytosol,Day),
  catalyst(9291,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9292),
  Day >= 1,
  in_compartment(Experiment,"C00670",cytosol,Day),
  in_compartment(Experiment,"C06015",cytosol,Day),
  catalyst(9292,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04517",cytosol,Day) :-
  not exclude(9292),
  Day >= 1,
  in_compartment(Experiment,"C00670",cytosol,Day),
  in_compartment(Experiment,"C06015",cytosol,Day),
  catalyst(9292,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00162",cytosol,Day) :-
  not exclude(9301),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C04233",cytosol,Day),
  catalyst(9301,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00670",cytosol,Day) :-
  not exclude(9301),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C04233",cytosol,Day),
  catalyst(9301,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9302),
  Day >= 1,
  in_compartment(Experiment,"C00162",cytosol,Day),
  in_compartment(Experiment,"C00670",cytosol,Day),
  catalyst(9302,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04233",cytosol,Day) :-
  not exclude(9302),
  Day >= 1,
  in_compartment(Experiment,"C00162",cytosol,Day),
  in_compartment(Experiment,"C00670",cytosol,Day),
  catalyst(9302,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9321),
  Day >= 1,
  in_compartment(Experiment,"C00060",cytosol,Day),
  in_compartment(Experiment,"C00670",cytosol,Day),
  catalyst(9321,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01178",cytosol,Day) :-
  not exclude(9321),
  Day >= 1,
  in_compartment(Experiment,"C00060",cytosol,Day),
  in_compartment(Experiment,"C00670",cytosol,Day),
  catalyst(9321,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00060",cytosol,Day) :-
  not exclude(9322),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C01178",cytosol,Day),
  catalyst(9322,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00670",cytosol,Day) :-
  not exclude(9322),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C01178",cytosol,Day),
  catalyst(9322,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00162",cytosol,Day) :-
  not exclude(9331),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00157",cytosol,Day),
  catalyst(9331,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00670",cytosol,Day) :-
  not exclude(9331),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00157",cytosol,Day),
  catalyst(9331,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9332),
  Day >= 1,
  in_compartment(Experiment,"C00162",cytosol,Day),
  in_compartment(Experiment,"C00670",cytosol,Day),
  catalyst(9332,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00157",cytosol,Day) :-
  not exclude(9332),
  Day >= 1,
  in_compartment(Experiment,"C00162",cytosol,Day),
  in_compartment(Experiment,"C00670",cytosol,Day),
  catalyst(9332,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00162",cytosol,Day) :-
  not exclude(9361),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00641",cytosol,Day),
  catalyst(9361,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01885",cytosol,Day) :-
  not exclude(9361),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00641",cytosol,Day),
  catalyst(9361,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9362),
  Day >= 1,
  in_compartment(Experiment,"C00162",cytosol,Day),
  in_compartment(Experiment,"C01885",cytosol,Day),
  catalyst(9362,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00641",cytosol,Day) :-
  not exclude(9362),
  Day >= 1,
  in_compartment(Experiment,"C00162",cytosol,Day),
  in_compartment(Experiment,"C01885",cytosol,Day),
  catalyst(9362,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00162",cytosol,Day) :-
  not exclude(9371),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00422",cytosol,Day),
  catalyst(9371,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00641",cytosol,Day) :-
  not exclude(9371),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00422",cytosol,Day),
  catalyst(9371,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9372),
  Day >= 1,
  in_compartment(Experiment,"C00162",cytosol,Day),
  in_compartment(Experiment,"C00641",cytosol,Day),
  catalyst(9372,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00422",cytosol,Day) :-
  not exclude(9372),
  Day >= 1,
  in_compartment(Experiment,"C00162",cytosol,Day),
  in_compartment(Experiment,"C00641",cytosol,Day),
  catalyst(9372,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00094",cytosol,Day) :-
  not exclude(9401),
  Day >= 1,
  in_compartment(Experiment,"C00320",cytosol,Day),
  in_compartment(Experiment,"C01326",cytosol,Day),
  catalyst(9401,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01755",cytosol,Day) :-
  not exclude(9401),
  Day >= 1,
  in_compartment(Experiment,"C00320",cytosol,Day),
  in_compartment(Experiment,"C01326",cytosol,Day),
  catalyst(9401,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00320",cytosol,Day) :-
  not exclude(9402),
  Day >= 1,
  in_compartment(Experiment,"C00094",cytosol,Day),
  in_compartment(Experiment,"C01755",cytosol,Day),
  catalyst(9402,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01326",cytosol,Day) :-
  not exclude(9402),
  Day >= 1,
  in_compartment(Experiment,"C00094",cytosol,Day),
  in_compartment(Experiment,"C01755",cytosol,Day),
  catalyst(9402,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00105",cytosol,Day) :-
  not exclude(9411),
  Day >= 1,
  in_compartment(Experiment,"C00043",cytosol,Day),
  in_compartment(Experiment,"C00110",cytosol,Day),
  catalyst(9411,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04500",cytosol,Day) :-
  not exclude(9411),
  Day >= 1,
  in_compartment(Experiment,"C00043",cytosol,Day),
  in_compartment(Experiment,"C00110",cytosol,Day),
  catalyst(9411,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00043",cytosol,Day) :-
  not exclude(9412),
  Day >= 1,
  in_compartment(Experiment,"C00105",cytosol,Day),
  in_compartment(Experiment,"C04500",cytosol,Day),
  catalyst(9412,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00110",cytosol,Day) :-
  not exclude(9412),
  Day >= 1,
  in_compartment(Experiment,"C00105",cytosol,Day),
  in_compartment(Experiment,"C04500",cytosol,Day),
  catalyst(9412,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(9421),
  Day >= 1,
  in_compartment(Experiment,"C00044",cytosol,Day),
  in_compartment(Experiment,"C02100",cytosol,Day),
  catalyst(9421,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02407",cytosol,Day) :-
  not exclude(9421),
  Day >= 1,
  in_compartment(Experiment,"C00044",cytosol,Day),
  in_compartment(Experiment,"C02100",cytosol,Day),
  catalyst(9421,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00044",cytosol,Day) :-
  not exclude(9422),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C02407",cytosol,Day),
  catalyst(9422,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02100",cytosol,Day) :-
  not exclude(9422),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C02407",cytosol,Day),
  catalyst(9422,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(9431),
  Day >= 1,
  in_compartment(Experiment,"C00039",cytosol,Day),
  in_compartment(Experiment,"C00677",cytosol,Day),
  catalyst(9431,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00039",cytosol,Day) :-
  not exclude(9431),
  Day >= 1,
  in_compartment(Experiment,"C00039",cytosol,Day),
  in_compartment(Experiment,"C00677",cytosol,Day),
  catalyst(9431,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00039",cytosol,Day) :-
  not exclude(9432),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00039",cytosol,Day),
  catalyst(9432,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00677",cytosol,Day) :-
  not exclude(9432),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00039",cytosol,Day),
  catalyst(9432,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(9441),
  Day >= 1,
  in_compartment(Experiment,"C00039",cytosol,Day),
  in_compartment(Experiment,"C00459",cytosol,Day),
  catalyst(9441,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00039",cytosol,Day) :-
  not exclude(9441),
  Day >= 1,
  in_compartment(Experiment,"C00039",cytosol,Day),
  in_compartment(Experiment,"C00459",cytosol,Day),
  catalyst(9441,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00039",cytosol,Day) :-
  not exclude(9442),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00039",cytosol,Day),
  catalyst(9442,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00459",cytosol,Day) :-
  not exclude(9442),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00039",cytosol,Day),
  catalyst(9442,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(9461),
  Day >= 1,
  in_compartment(Experiment,"C00039",cytosol,Day),
  in_compartment(Experiment,"C00286",cytosol,Day),
  catalyst(9461,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00039",cytosol,Day) :-
  not exclude(9461),
  Day >= 1,
  in_compartment(Experiment,"C00039",cytosol,Day),
  in_compartment(Experiment,"C00286",cytosol,Day),
  catalyst(9461,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00039",cytosol,Day) :-
  not exclude(9462),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00039",cytosol,Day),
  catalyst(9462,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00286",cytosol,Day) :-
  not exclude(9462),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00039",cytosol,Day),
  catalyst(9462,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(9471),
  Day >= 1,
  in_compartment(Experiment,"C00039",cytosol,Day),
  in_compartment(Experiment,"C00131",cytosol,Day),
  catalyst(9471,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00039",cytosol,Day) :-
  not exclude(9471),
  Day >= 1,
  in_compartment(Experiment,"C00039",cytosol,Day),
  in_compartment(Experiment,"C00131",cytosol,Day),
  catalyst(9471,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00039",cytosol,Day) :-
  not exclude(9472),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00039",cytosol,Day),
  catalyst(9472,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00131",cytosol,Day) :-
  not exclude(9472),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00039",cytosol,Day),
  catalyst(9472,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(9481),
  Day >= 1,
  in_compartment(Experiment,"C00046",cytosol,Day),
  in_compartment(Experiment,"C00201",cytosol,Day),
  catalyst(9481,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00046",cytosol,Day) :-
  not exclude(9481),
  Day >= 1,
  in_compartment(Experiment,"C00046",cytosol,Day),
  in_compartment(Experiment,"C00201",cytosol,Day),
  catalyst(9481,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00046",cytosol,Day) :-
  not exclude(9482),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00046",cytosol,Day),
  catalyst(9482,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00201",cytosol,Day) :-
  not exclude(9482),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00046",cytosol,Day),
  catalyst(9482,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(9491),
  Day >= 1,
  in_compartment(Experiment,"C00046",cytosol,Day),
  in_compartment(Experiment,"C00075",cytosol,Day),
  catalyst(9491,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00046",cytosol,Day) :-
  not exclude(9491),
  Day >= 1,
  in_compartment(Experiment,"C00046",cytosol,Day),
  in_compartment(Experiment,"C00075",cytosol,Day),
  catalyst(9491,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00046",cytosol,Day) :-
  not exclude(9492),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00046",cytosol,Day),
  catalyst(9492,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00075",cytosol,Day) :-
  not exclude(9492),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00046",cytosol,Day),
  catalyst(9492,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(9501),
  Day >= 1,
  in_compartment(Experiment,"C00046",cytosol,Day),
  in_compartment(Experiment,"C00063",cytosol,Day),
  catalyst(9501,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00046",cytosol,Day) :-
  not exclude(9501),
  Day >= 1,
  in_compartment(Experiment,"C00046",cytosol,Day),
  in_compartment(Experiment,"C00063",cytosol,Day),
  catalyst(9501,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00046",cytosol,Day) :-
  not exclude(9502),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00046",cytosol,Day),
  catalyst(9502,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00063",cytosol,Day) :-
  not exclude(9502),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00046",cytosol,Day),
  catalyst(9502,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(9521),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00046",cytosol,Day),
  catalyst(9521,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00046",cytosol,Day) :-
  not exclude(9521),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00046",cytosol,Day),
  catalyst(9521,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(9522),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00046",cytosol,Day),
  catalyst(9522,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00046",cytosol,Day) :-
  not exclude(9522),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00046",cytosol,Day),
  catalyst(9522,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(9531),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01185",cytosol,Day),
  catalyst(9531,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00857",cytosol,Day) :-
  not exclude(9531),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C01185",cytosol,Day),
  catalyst(9531,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(9532),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00857",cytosol,Day),
  catalyst(9532,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01185",cytosol,Day) :-
  not exclude(9532),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C00857",cytosol,Day),
  catalyst(9532,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(9561),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00017",cytosol,Day),
  catalyst(9561,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00562",cytosol,Day) :-
  not exclude(9561),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00017",cytosol,Day),
  catalyst(9561,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(9562),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00562",cytosol,Day),
  catalyst(9562,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00017",cytosol,Day) :-
  not exclude(9562),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00562",cytosol,Day),
  catalyst(9562,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(9581),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00124",cytosol,Day),
  catalyst(9581,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00446",cytosol,Day) :-
  not exclude(9581),
  Day >= 1,
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00124",cytosol,Day),
  catalyst(9581,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(9582),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00446",cytosol,Day),
  catalyst(9582,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00124",cytosol,Day) :-
  not exclude(9582),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00446",cytosol,Day),
  catalyst(9582,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",cytosol,Day) :-
  not exclude(9591),
  Day >= 1,
  in_compartment(Experiment,"C05688",cytosol,Day),
  in_compartment(Experiment,"C05701",cytosol,Day),
  catalyst(9591,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05699",cytosol,Day) :-
  not exclude(9591),
  Day >= 1,
  in_compartment(Experiment,"C05688",cytosol,Day),
  in_compartment(Experiment,"C05701",cytosol,Day),
  catalyst(9591,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05688",cytosol,Day) :-
  not exclude(9592),
  Day >= 1,
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C05699",cytosol,Day),
  catalyst(9592,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05701",cytosol,Day) :-
  not exclude(9592),
  Day >= 1,
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C05699",cytosol,Day),
  catalyst(9592,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(9611),
  Day >= 1,
  in_compartment(Experiment,"C05688",cytosol,Day),
  in_compartment(Experiment,"C05702",cytosol,Day),
  catalyst(9611,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05699",cytosol,Day) :-
  not exclude(9611),
  Day >= 1,
  in_compartment(Experiment,"C05688",cytosol,Day),
  in_compartment(Experiment,"C05702",cytosol,Day),
  catalyst(9611,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05688",cytosol,Day) :-
  not exclude(9612),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C05699",cytosol,Day),
  catalyst(9612,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05702",cytosol,Day) :-
  not exclude(9612),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C05699",cytosol,Day),
  catalyst(9612,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",cytosol,Day) :-
  not exclude(9621),
  Day >= 1,
  in_compartment(Experiment,"C00097",cytosol,Day),
  in_compartment(Experiment,"C01118",cytosol,Day),
  catalyst(9621,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02291",cytosol,Day) :-
  not exclude(9621),
  Day >= 1,
  in_compartment(Experiment,"C00097",cytosol,Day),
  in_compartment(Experiment,"C01118",cytosol,Day),
  catalyst(9621,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00097",cytosol,Day) :-
  not exclude(9622),
  Day >= 1,
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C02291",cytosol,Day),
  catalyst(9622,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01118",cytosol,Day) :-
  not exclude(9622),
  Day >= 1,
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C02291",cytosol,Day),
  catalyst(9622,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00033",cytosol,Day) :-
  not exclude(9631),
  Day >= 1,
  in_compartment(Experiment,"C00320",cytosol,Day),
  in_compartment(Experiment,"C00979",cytosol,Day),
  catalyst(9631,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05824",cytosol,Day) :-
  not exclude(9631),
  Day >= 1,
  in_compartment(Experiment,"C00320",cytosol,Day),
  in_compartment(Experiment,"C00979",cytosol,Day),
  catalyst(9631,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00320",cytosol,Day) :-
  not exclude(9632),
  Day >= 1,
  in_compartment(Experiment,"C00033",cytosol,Day),
  in_compartment(Experiment,"C05824",cytosol,Day),
  catalyst(9632,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00979",cytosol,Day) :-
  not exclude(9632),
  Day >= 1,
  in_compartment(Experiment,"C00033",cytosol,Day),
  in_compartment(Experiment,"C05824",cytosol,Day),
  catalyst(9632,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00097",cytosol,Day) :-
  not exclude(9641),
  Day >= 1,
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C00542",cytosol,Day),
  catalyst(9641,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01118",cytosol,Day) :-
  not exclude(9641),
  Day >= 1,
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C00542",cytosol,Day),
  catalyst(9641,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",cytosol,Day) :-
  not exclude(9642),
  Day >= 1,
  in_compartment(Experiment,"C00097",cytosol,Day),
  in_compartment(Experiment,"C01118",cytosol,Day),
  catalyst(9642,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00542",cytosol,Day) :-
  not exclude(9642),
  Day >= 1,
  in_compartment(Experiment,"C00097",cytosol,Day),
  in_compartment(Experiment,"C01118",cytosol,Day),
  catalyst(9642,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",cytosol,Day) :-
  not exclude(9651),
  Day >= 1,
  in_compartment(Experiment,"C00297",cytosol,Day),
  in_compartment(Experiment,"C01118",cytosol,Day),
  catalyst(9651,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00155",cytosol,Day) :-
  not exclude(9651),
  Day >= 1,
  in_compartment(Experiment,"C00297",cytosol,Day),
  in_compartment(Experiment,"C01118",cytosol,Day),
  catalyst(9651,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00297",cytosol,Day) :-
  not exclude(9652),
  Day >= 1,
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C00155",cytosol,Day),
  catalyst(9652,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01118",cytosol,Day) :-
  not exclude(9652),
  Day >= 1,
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C00155",cytosol,Day),
  catalyst(9652,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00014",cytosol,Day) :-
  not exclude(9661),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C01118",cytosol,Day),
  catalyst(9661,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00042",cytosol,Day) :-
  not exclude(9661),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C01118",cytosol,Day),
  catalyst(9661,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00109",cytosol,Day) :-
  not exclude(9661),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C01118",cytosol,Day),
  catalyst(9661,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9662),
  Day >= 1,
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C00109",cytosol,Day),
  catalyst(9662,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01118",cytosol,Day) :-
  not exclude(9662),
  Day >= 1,
  in_compartment(Experiment,"C00014",cytosol,Day),
  in_compartment(Experiment,"C00042",cytosol,Day),
  in_compartment(Experiment,"C00109",cytosol,Day),
  catalyst(9662,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00986",cytosol,Day) :-
  not exclude(9671),
  Day >= 1,
  in_compartment(Experiment,"C00315",cytosol,Day),
  in_compartment(Experiment,"C07281",cytosol,Day),
  catalyst(9671,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C07282",cytosol,Day) :-
  not exclude(9671),
  Day >= 1,
  in_compartment(Experiment,"C00315",cytosol,Day),
  in_compartment(Experiment,"C07281",cytosol,Day),
  catalyst(9671,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00315",cytosol,Day) :-
  not exclude(9672),
  Day >= 1,
  in_compartment(Experiment,"C00986",cytosol,Day),
  in_compartment(Experiment,"C07282",cytosol,Day),
  catalyst(9672,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C07281",cytosol,Day) :-
  not exclude(9672),
  Day >= 1,
  in_compartment(Experiment,"C00986",cytosol,Day),
  in_compartment(Experiment,"C07282",cytosol,Day),
  catalyst(9672,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00013",cytosol,Day) :-
  not exclude(9681),
  Day >= 1,
  in_compartment(Experiment,"C00066",cytosol,Day),
  in_compartment(Experiment,"C00129",cytosol,Day),
  catalyst(9681,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04432",cytosol,Day) :-
  not exclude(9681),
  Day >= 1,
  in_compartment(Experiment,"C00066",cytosol,Day),
  in_compartment(Experiment,"C00129",cytosol,Day),
  catalyst(9681,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00066",cytosol,Day) :-
  not exclude(9682),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C04432",cytosol,Day),
  catalyst(9682,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00129",cytosol,Day) :-
  not exclude(9682),
  Day >= 1,
  in_compartment(Experiment,"C00013",cytosol,Day),
  in_compartment(Experiment,"C04432",cytosol,Day),
  catalyst(9682,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00035",cytosol,Day) :-
  not exclude(9691),
  Day >= 1,
  in_compartment(Experiment,"C00096",cytosol,Day),
  in_compartment(Experiment,"C05863",cytosol,Day),
  catalyst(9691,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05864",cytosol,Day) :-
  not exclude(9691),
  Day >= 1,
  in_compartment(Experiment,"C00096",cytosol,Day),
  in_compartment(Experiment,"C05863",cytosol,Day),
  catalyst(9691,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00096",cytosol,Day) :-
  not exclude(9692),
  Day >= 1,
  in_compartment(Experiment,"C00035",cytosol,Day),
  in_compartment(Experiment,"C05864",cytosol,Day),
  catalyst(9692,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05863",cytosol,Day) :-
  not exclude(9692),
  Day >= 1,
  in_compartment(Experiment,"C00035",cytosol,Day),
  in_compartment(Experiment,"C05864",cytosol,Day),
  catalyst(9692,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00621",cytosol,Day) :-
  not exclude(9711),
  Day >= 1,
  in_compartment(Experiment,"C03021",cytosol,Day),
  in_compartment(Experiment,"C05872",cytosol,Day),
  catalyst(9711,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05873",cytosol,Day) :-
  not exclude(9711),
  Day >= 1,
  in_compartment(Experiment,"C03021",cytosol,Day),
  in_compartment(Experiment,"C05872",cytosol,Day),
  catalyst(9711,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03021",cytosol,Day) :-
  not exclude(9712),
  Day >= 1,
  in_compartment(Experiment,"C00621",cytosol,Day),
  in_compartment(Experiment,"C05873",cytosol,Day),
  catalyst(9712,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05872",cytosol,Day) :-
  not exclude(9712),
  Day >= 1,
  in_compartment(Experiment,"C00621",cytosol,Day),
  in_compartment(Experiment,"C05873",cytosol,Day),
  catalyst(9712,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00015",cytosol,Day) :-
  not exclude(9731),
  Day >= 1,
  in_compartment(Experiment,"C00029",cytosol,Day),
  in_compartment(Experiment,"C00110",cytosol,Day),
  catalyst(9731,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01246",cytosol,Day) :-
  not exclude(9731),
  Day >= 1,
  in_compartment(Experiment,"C00029",cytosol,Day),
  in_compartment(Experiment,"C00110",cytosol,Day),
  catalyst(9731,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00029",cytosol,Day) :-
  not exclude(9732),
  Day >= 1,
  in_compartment(Experiment,"C00015",cytosol,Day),
  in_compartment(Experiment,"C01246",cytosol,Day),
  catalyst(9732,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00110",cytosol,Day) :-
  not exclude(9732),
  Day >= 1,
  in_compartment(Experiment,"C00015",cytosol,Day),
  in_compartment(Experiment,"C01246",cytosol,Day),
  catalyst(9732,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00066",cytosol,Day) :-
  not exclude(9751),
  Day >= 1,
  in_compartment(Experiment,"C00017",cytosol,Day),
  in_compartment(Experiment,"C02163",cytosol,Day),
  catalyst(9751,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02550",cytosol,Day) :-
  not exclude(9751),
  Day >= 1,
  in_compartment(Experiment,"C00017",cytosol,Day),
  in_compartment(Experiment,"C02163",cytosol,Day),
  catalyst(9751,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00017",cytosol,Day) :-
  not exclude(9752),
  Day >= 1,
  in_compartment(Experiment,"C00066",cytosol,Day),
  in_compartment(Experiment,"C02550",cytosol,Day),
  catalyst(9752,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02163",cytosol,Day) :-
  not exclude(9752),
  Day >= 1,
  in_compartment(Experiment,"C00066",cytosol,Day),
  in_compartment(Experiment,"C02550",cytosol,Day),
  catalyst(9752,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9771),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00083",cytosol,Day),
  catalyst(9771,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(9771),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00083",cytosol,Day),
  catalyst(9771,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(9771),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00083",cytosol,Day),
  catalyst(9771,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(9771),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00083",cytosol,Day),
  catalyst(9771,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02843",cytosol,Day) :-
  not exclude(9771),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00083",cytosol,Day),
  catalyst(9771,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(9772),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C02843",cytosol,Day),
  catalyst(9772,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00024",cytosol,Day) :-
  not exclude(9772),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C02843",cytosol,Day),
  catalyst(9772,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(9772),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C02843",cytosol,Day),
  catalyst(9772,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00083",cytosol,Day) :-
  not exclude(9772),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C02843",cytosol,Day),
  catalyst(9772,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(9791),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05761",cytosol,Day),
  catalyst(9791,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05760",cytosol,Day) :-
  not exclude(9791),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05761",cytosol,Day),
  catalyst(9791,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(9792),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C05760",cytosol,Day),
  catalyst(9792,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05761",cytosol,Day) :-
  not exclude(9792),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C05760",cytosol,Day),
  catalyst(9792,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9801),
  Day >= 1,
  in_compartment(Experiment,"C05757",cytosol,Day),
  catalyst(9801,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05758",cytosol,Day) :-
  not exclude(9801),
  Day >= 1,
  in_compartment(Experiment,"C05757",cytosol,Day),
  catalyst(9801,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05757",cytosol,Day) :-
  not exclude(9802),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C05758",cytosol,Day),
  catalyst(9802,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(9811),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05755",cytosol,Day),
  catalyst(9811,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05754",cytosol,Day) :-
  not exclude(9811),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05755",cytosol,Day),
  catalyst(9811,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(9812),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C05754",cytosol,Day),
  catalyst(9812,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05755",cytosol,Day) :-
  not exclude(9812),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C05754",cytosol,Day),
  catalyst(9812,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(9821),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05752",cytosol,Day),
  catalyst(9821,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05751",cytosol,Day) :-
  not exclude(9821),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05752",cytosol,Day),
  catalyst(9821,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(9822),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C05751",cytosol,Day),
  catalyst(9822,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05752",cytosol,Day) :-
  not exclude(9822),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C05751",cytosol,Day),
  catalyst(9822,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9841),
  Day >= 1,
  in_compartment(Experiment,"C05747",cytosol,Day),
  catalyst(9841,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05748",cytosol,Day) :-
  not exclude(9841),
  Day >= 1,
  in_compartment(Experiment,"C05747",cytosol,Day),
  catalyst(9841,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05747",cytosol,Day) :-
  not exclude(9842),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C05748",cytosol,Day),
  catalyst(9842,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(9851),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05223",cytosol,Day),
  catalyst(9851,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05758",cytosol,Day) :-
  not exclude(9851),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05223",cytosol,Day),
  catalyst(9851,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(9852),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C05758",cytosol,Day),
  catalyst(9852,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05223",cytosol,Day) :-
  not exclude(9852),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C05758",cytosol,Day),
  catalyst(9852,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9861),
  Day >= 1,
  in_compartment(Experiment,"C04688",cytosol,Day),
  catalyst(9861,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05760",cytosol,Day) :-
  not exclude(9861),
  Day >= 1,
  in_compartment(Experiment,"C04688",cytosol,Day),
  catalyst(9861,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04688",cytosol,Day) :-
  not exclude(9862),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C05760",cytosol,Day),
  catalyst(9862,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9871),
  Day >= 1,
  in_compartment(Experiment,"C04633",cytosol,Day),
  catalyst(9871,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05763",cytosol,Day) :-
  not exclude(9871),
  Day >= 1,
  in_compartment(Experiment,"C04633",cytosol,Day),
  catalyst(9871,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04633",cytosol,Day) :-
  not exclude(9872),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C05763",cytosol,Day),
  catalyst(9872,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9881),
  Day >= 1,
  in_compartment(Experiment,"C04620",cytosol,Day),
  catalyst(9881,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05751",cytosol,Day) :-
  not exclude(9881),
  Day >= 1,
  in_compartment(Experiment,"C04620",cytosol,Day),
  catalyst(9881,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04620",cytosol,Day) :-
  not exclude(9882),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C05751",cytosol,Day),
  catalyst(9882,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(9891),
  Day >= 1,
  in_compartment(Experiment,"C04619",cytosol,Day),
  catalyst(9891,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05754",cytosol,Day) :-
  not exclude(9891),
  Day >= 1,
  in_compartment(Experiment,"C04619",cytosol,Day),
  catalyst(9891,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04619",cytosol,Day) :-
  not exclude(9892),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C05754",cytosol,Day),
  catalyst(9892,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(9901),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05745",cytosol,Day),
  catalyst(9901,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04246",cytosol,Day) :-
  not exclude(9901),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05745",cytosol,Day),
  catalyst(9901,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(9902),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C04246",cytosol,Day),
  catalyst(9902,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05745",cytosol,Day) :-
  not exclude(9902),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C04246",cytosol,Day),
  catalyst(9902,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(9921),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00069",cytosol,Day),
  catalyst(9921,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01883",cytosol,Day) :-
  not exclude(9921),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00069",cytosol,Day),
  catalyst(9921,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00024",cytosol,Day) :-
  not exclude(9922),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C01883",cytosol,Day),
  catalyst(9922,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00069",cytosol,Day) :-
  not exclude(9922),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C01883",cytosol,Day),
  catalyst(9922,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(9931),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C01429",cytosol,Day),
  catalyst(9931,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01997",cytosol,Day) :-
  not exclude(9931),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C01429",cytosol,Day),
  catalyst(9931,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00024",cytosol,Day) :-
  not exclude(9932),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C01997",cytosol,Day),
  catalyst(9932,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01429",cytosol,Day) :-
  not exclude(9932),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C01997",cytosol,Day),
  catalyst(9932,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(9941),
  Day >= 1,
  in_compartment(Experiment,"C00040",cytosol,Day),
  in_compartment(Experiment,"C00187",cytosol,Day),
  catalyst(9941,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02530",cytosol,Day) :-
  not exclude(9941),
  Day >= 1,
  in_compartment(Experiment,"C00040",cytosol,Day),
  in_compartment(Experiment,"C00187",cytosol,Day),
  catalyst(9941,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00040",cytosol,Day) :-
  not exclude(9942),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C02530",cytosol,Day),
  catalyst(9942,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00187",cytosol,Day) :-
  not exclude(9942),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C02530",cytosol,Day),
  catalyst(9942,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",cytosol,Day) :-
  not exclude(9951),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C05200",cytosol,Day),
  catalyst(9951,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05313",cytosol,Day) :-
  not exclude(9951),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C05200",cytosol,Day),
  catalyst(9951,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00019",cytosol,Day) :-
  not exclude(9952),
  Day >= 1,
  in_compartment(Experiment,"C00021",cytosol,Day),
  in_compartment(Experiment,"C05313",cytosol,Day),
  catalyst(9952,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05200",cytosol,Day) :-
  not exclude(9952),
  Day >= 1,
  in_compartment(Experiment,"C00021",cytosol,Day),
  in_compartment(Experiment,"C05313",cytosol,Day),
  catalyst(9952,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",cytosol,Day) :-
  not exclude(9961),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C04506",cytosol,Day),
  catalyst(9961,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04748",cytosol,Day) :-
  not exclude(9961),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C04506",cytosol,Day),
  catalyst(9961,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00019",cytosol,Day) :-
  not exclude(9962),
  Day >= 1,
  in_compartment(Experiment,"C00021",cytosol,Day),
  in_compartment(Experiment,"C04748",cytosol,Day),
  catalyst(9962,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04506",cytosol,Day) :-
  not exclude(9962),
  Day >= 1,
  in_compartment(Experiment,"C00021",cytosol,Day),
  in_compartment(Experiment,"C04748",cytosol,Day),
  catalyst(9962,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00021",cytosol,Day) :-
  not exclude(9981),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C00066",cytosol,Day),
  catalyst(9981,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04728",cytosol,Day) :-
  not exclude(9981),
  Day >= 1,
  in_compartment(Experiment,"C00019",cytosol,Day),
  in_compartment(Experiment,"C00066",cytosol,Day),
  catalyst(9981,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00019",cytosol,Day) :-
  not exclude(9982),
  Day >= 1,
  in_compartment(Experiment,"C00021",cytosol,Day),
  in_compartment(Experiment,"C04728",cytosol,Day),
  catalyst(9982,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00066",cytosol,Day) :-
  not exclude(9982),
  Day >= 1,
  in_compartment(Experiment,"C00021",cytosol,Day),
  in_compartment(Experiment,"C04728",cytosol,Day),
  catalyst(9982,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",cytosol,Day) :-
  not exclude(10011),
  Day >= 1,
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00704",cytosol,Day),
  catalyst(10011,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00027",cytosol,Day) :-
  not exclude(10011),
  Day >= 1,
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00704",cytosol,Day),
  catalyst(10011,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10012),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00027",cytosol,Day),
  catalyst(10012,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00704",cytosol,Day) :-
  not exclude(10012),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00027",cytosol,Day),
  catalyst(10012,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(10021),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00030",cytosol,Day),
  in_compartment(Experiment,"C00412",cytosol,Day),
  catalyst(10021,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00028",cytosol,Day) :-
  not exclude(10021),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00030",cytosol,Day),
  in_compartment(Experiment,"C00412",cytosol,Day),
  catalyst(10021,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00510",cytosol,Day) :-
  not exclude(10021),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00030",cytosol,Day),
  in_compartment(Experiment,"C00412",cytosol,Day),
  catalyst(10021,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",cytosol,Day) :-
  not exclude(10022),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00028",cytosol,Day),
  in_compartment(Experiment,"C00510",cytosol,Day),
  catalyst(10022,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00030",cytosol,Day) :-
  not exclude(10022),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00028",cytosol,Day),
  in_compartment(Experiment,"C00510",cytosol,Day),
  catalyst(10022,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00412",cytosol,Day) :-
  not exclude(10022),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00028",cytosol,Day),
  in_compartment(Experiment,"C00510",cytosol,Day),
  catalyst(10022,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00283",cytosol,Day) :-
  not exclude(10031),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C06604",cytosol,Day),
  catalyst(10031,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C06606",cytosol,Day) :-
  not exclude(10031),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C06604",cytosol,Day),
  catalyst(10031,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(10032),
  Day >= 1,
  in_compartment(Experiment,"C00283",cytosol,Day),
  in_compartment(Experiment,"C06606",cytosol,Day),
  catalyst(10032,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C06604",cytosol,Day) :-
  not exclude(10032),
  Day >= 1,
  in_compartment(Experiment,"C00283",cytosol,Day),
  in_compartment(Experiment,"C06606",cytosol,Day),
  catalyst(10032,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(10051),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00162",cytosol,Day),
  in_compartment(Experiment,"C03024",cytosol,Day),
  catalyst(10051,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03161",cytosol,Day) :-
  not exclude(10051),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00162",cytosol,Day),
  in_compartment(Experiment,"C03024",cytosol,Day),
  catalyst(10051,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05102",cytosol,Day) :-
  not exclude(10051),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00162",cytosol,Day),
  in_compartment(Experiment,"C03024",cytosol,Day),
  catalyst(10051,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",cytosol,Day) :-
  not exclude(10052),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C03161",cytosol,Day),
  in_compartment(Experiment,"C05102",cytosol,Day),
  catalyst(10052,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00162",cytosol,Day) :-
  not exclude(10052),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C03161",cytosol,Day),
  in_compartment(Experiment,"C05102",cytosol,Day),
  catalyst(10052,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03024",cytosol,Day) :-
  not exclude(10052),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C03161",cytosol,Day),
  in_compartment(Experiment,"C05102",cytosol,Day),
  catalyst(10052,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(10061),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C01598",cytosol,Day),
  in_compartment(Experiment,"C03024",cytosol,Day),
  catalyst(10061,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03161",cytosol,Day) :-
  not exclude(10061),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C01598",cytosol,Day),
  in_compartment(Experiment,"C03024",cytosol,Day),
  catalyst(10061,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05643",cytosol,Day) :-
  not exclude(10061),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C01598",cytosol,Day),
  in_compartment(Experiment,"C03024",cytosol,Day),
  catalyst(10061,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",cytosol,Day) :-
  not exclude(10062),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C03161",cytosol,Day),
  in_compartment(Experiment,"C05643",cytosol,Day),
  catalyst(10062,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01598",cytosol,Day) :-
  not exclude(10062),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C03161",cytosol,Day),
  in_compartment(Experiment,"C05643",cytosol,Day),
  catalyst(10062,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03024",cytosol,Day) :-
  not exclude(10062),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C03161",cytosol,Day),
  in_compartment(Experiment,"C05643",cytosol,Day),
  catalyst(10062,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(10071),
  Day >= 1,
  in_compartment(Experiment,"C00027",cytosol,Day),
  in_compartment(Experiment,"C00126",cytosol,Day),
  catalyst(10071,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00125",cytosol,Day) :-
  not exclude(10071),
  Day >= 1,
  in_compartment(Experiment,"C00027",cytosol,Day),
  in_compartment(Experiment,"C00126",cytosol,Day),
  catalyst(10071,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00027",cytosol,Day) :-
  not exclude(10072),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00125",cytosol,Day),
  catalyst(10072,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00126",cytosol,Day) :-
  not exclude(10072),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00125",cytosol,Day),
  catalyst(10072,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00342",cytosol,Day) :-
  not exclude(10081),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00343",cytosol,Day),
  in_compartment(Experiment,"C03023",cytosol,Day),
  catalyst(10081,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03895",cytosol,Day) :-
  not exclude(10081),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00343",cytosol,Day),
  in_compartment(Experiment,"C03023",cytosol,Day),
  catalyst(10081,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(10082),
  Day >= 1,
  in_compartment(Experiment,"C00342",cytosol,Day),
  in_compartment(Experiment,"C03895",cytosol,Day),
  catalyst(10082,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00343",cytosol,Day) :-
  not exclude(10082),
  Day >= 1,
  in_compartment(Experiment,"C00342",cytosol,Day),
  in_compartment(Experiment,"C03895",cytosol,Day),
  catalyst(10082,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03023",cytosol,Day) :-
  not exclude(10082),
  Day >= 1,
  in_compartment(Experiment,"C00342",cytosol,Day),
  in_compartment(Experiment,"C03895",cytosol,Day),
  catalyst(10082,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10091),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C02972",cytosol,Day),
  catalyst(10091,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02051",cytosol,Day) :-
  not exclude(10091),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C02972",cytosol,Day),
  catalyst(10091,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10092),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C02051",cytosol,Day),
  catalyst(10092,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C02972",cytosol,Day) :-
  not exclude(10092),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C02051",cytosol,Day),
  catalyst(10092,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(10131),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00028",cytosol,Day),
  catalyst(10131,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00030",cytosol,Day) :-
  not exclude(10131),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00028",cytosol,Day),
  catalyst(10131,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(10132),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00030",cytosol,Day),
  catalyst(10132,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00028",cytosol,Day) :-
  not exclude(10132),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00030",cytosol,Day),
  catalyst(10132,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10151),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00472",cytosol,Day),
  catalyst(10151,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05309",cytosol,Day) :-
  not exclude(10151),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00472",cytosol,Day),
  catalyst(10151,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10152),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C05309",cytosol,Day),
  catalyst(10152,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00472",cytosol,Day) :-
  not exclude(10152),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C05309",cytosol,Day),
  catalyst(10152,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(10161),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00996",cytosol,Day),
  catalyst(10161,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00999",cytosol,Day) :-
  not exclude(10161),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00996",cytosol,Day),
  catalyst(10161,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(10162),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00999",cytosol,Day),
  catalyst(10162,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00996",cytosol,Day) :-
  not exclude(10162),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00999",cytosol,Day),
  catalyst(10162,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10181),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(10181,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(10181),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(10181,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00064",cytosol,Day) :-
  not exclude(10181),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  catalyst(10181,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10182),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  catalyst(10182,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(10182),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  catalyst(10182,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10201),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C01694",cytosol,Day),
  catalyst(10201,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10201),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C01694",cytosol,Day),
  catalyst(10201,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05440",cytosol,Day) :-
  not exclude(10201),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C01694",cytosol,Day),
  catalyst(10201,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10202),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C05440",cytosol,Day),
  catalyst(10202,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01694",cytosol,Day) :-
  not exclude(10202),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C05440",cytosol,Day),
  catalyst(10202,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10221),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C01724",cytosol,Day),
  catalyst(10221,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00058",cytosol,Day) :-
  not exclude(10221),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C01724",cytosol,Day),
  catalyst(10221,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05108",cytosol,Day) :-
  not exclude(10221),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C01724",cytosol,Day),
  catalyst(10221,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10222),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00058",cytosol,Day),
  in_compartment(Experiment,"C05108",cytosol,Day),
  catalyst(10222,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",cytosol,Day) :-
  not exclude(10222),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00058",cytosol,Day),
  in_compartment(Experiment,"C05108",cytosol,Day),
  catalyst(10222,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10222),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00058",cytosol,Day),
  in_compartment(Experiment,"C05108",cytosol,Day),
  catalyst(10222,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01724",cytosol,Day) :-
  not exclude(10222),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00058",cytosol,Day),
  in_compartment(Experiment,"C05108",cytosol,Day),
  catalyst(10222,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(10241),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C05488",cytosol,Day),
  catalyst(10241,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05487",cytosol,Day) :-
  not exclude(10241),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C05488",cytosol,Day),
  catalyst(10241,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(10242),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05487",cytosol,Day),
  catalyst(10242,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10242),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05487",cytosol,Day),
  catalyst(10242,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05488",cytosol,Day) :-
  not exclude(10242),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05487",cytosol,Day),
  catalyst(10242,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10251),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C05140",cytosol,Day),
  catalyst(10251,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05139",cytosol,Day) :-
  not exclude(10251),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C05140",cytosol,Day),
  catalyst(10251,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10252),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C05139",cytosol,Day),
  catalyst(10252,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10252),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C05139",cytosol,Day),
  catalyst(10252,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05140",cytosol,Day) :-
  not exclude(10252),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C05139",cytosol,Day),
  catalyst(10252,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(10261),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C05140",cytosol,Day),
  catalyst(10261,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05139",cytosol,Day) :-
  not exclude(10261),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C05140",cytosol,Day),
  catalyst(10261,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(10262),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05139",cytosol,Day),
  catalyst(10262,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10262),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05139",cytosol,Day),
  catalyst(10262,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05140",cytosol,Day) :-
  not exclude(10262),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05139",cytosol,Day),
  catalyst(10262,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(10281),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05485",cytosol,Day),
  catalyst(10281,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10281),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05485",cytosol,Day),
  catalyst(10281,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03205",cytosol,Day) :-
  not exclude(10281),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05485",cytosol,Day),
  catalyst(10281,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(10282),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C03205",cytosol,Day),
  catalyst(10282,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05485",cytosol,Day) :-
  not exclude(10282),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C03205",cytosol,Day),
  catalyst(10282,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10291),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C05138",cytosol,Day),
  catalyst(10291,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10291),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C05138",cytosol,Day),
  catalyst(10291,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01176",cytosol,Day) :-
  not exclude(10291),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C05138",cytosol,Day),
  catalyst(10291,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10292),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C01176",cytosol,Day),
  catalyst(10292,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05138",cytosol,Day) :-
  not exclude(10292),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C01176",cytosol,Day),
  catalyst(10292,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(10301),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05138",cytosol,Day),
  catalyst(10301,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10301),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05138",cytosol,Day),
  catalyst(10301,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01176",cytosol,Day) :-
  not exclude(10301),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05138",cytosol,Day),
  catalyst(10301,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(10302),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C01176",cytosol,Day),
  catalyst(10302,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05138",cytosol,Day) :-
  not exclude(10302),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C01176",cytosol,Day),
  catalyst(10302,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(10321),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00735",cytosol,Day),
  catalyst(10321,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05489",cytosol,Day) :-
  not exclude(10321),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00735",cytosol,Day),
  catalyst(10321,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(10322),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05489",cytosol,Day),
  catalyst(10322,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10322),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05489",cytosol,Day),
  catalyst(10322,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00735",cytosol,Day) :-
  not exclude(10322),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C05489",cytosol,Day),
  catalyst(10322,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10331),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00535",cytosol,Day),
  catalyst(10331,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04295",cytosol,Day) :-
  not exclude(10331),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00535",cytosol,Day),
  catalyst(10331,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10332),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C04295",cytosol,Day),
  catalyst(10332,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10332),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C04295",cytosol,Day),
  catalyst(10332,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00535",cytosol,Day) :-
  not exclude(10332),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C04295",cytosol,Day),
  catalyst(10332,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10351),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C01953",cytosol,Day),
  catalyst(10351,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10351),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C01953",cytosol,Day),
  catalyst(10351,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00410",cytosol,Day) :-
  not exclude(10351),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C01953",cytosol,Day),
  catalyst(10351,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10352),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00410",cytosol,Day),
  catalyst(10352,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01953",cytosol,Day) :-
  not exclude(10352),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00410",cytosol,Day),
  catalyst(10352,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10371),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C01227",cytosol,Day),
  catalyst(10371,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10371),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C01227",cytosol,Day),
  catalyst(10371,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00280",cytosol,Day) :-
  not exclude(10371),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C01227",cytosol,Day),
  catalyst(10371,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10372),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00280",cytosol,Day),
  catalyst(10372,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01227",cytosol,Day) :-
  not exclude(10372),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00280",cytosol,Day),
  catalyst(10372,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(10391),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00216",cytosol,Day),
  catalyst(10391,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00652",cytosol,Day) :-
  not exclude(10391),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00216",cytosol,Day),
  catalyst(10391,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(10392),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00652",cytosol,Day),
  catalyst(10392,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00216",cytosol,Day) :-
  not exclude(10392),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00652",cytosol,Day),
  catalyst(10392,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(10401),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00288",cytosol,Day),
  catalyst(10401,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(10401),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00288",cytosol,Day),
  catalyst(10401,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00025",cytosol,Day) :-
  not exclude(10401),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00288",cytosol,Day),
  catalyst(10401,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00169",cytosol,Day) :-
  not exclude(10401),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00002",cytosol,Day),
  in_compartment(Experiment,"C00064",cytosol,Day),
  in_compartment(Experiment,"C00288",cytosol,Day),
  catalyst(10401,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(10402),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00169",cytosol,Day),
  catalyst(10402,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(10402),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00169",cytosol,Day),
  catalyst(10402,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00064",cytosol,Day) :-
  not exclude(10402),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00169",cytosol,Day),
  catalyst(10402,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00288",cytosol,Day) :-
  not exclude(10402),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C00025",cytosol,Day),
  in_compartment(Experiment,"C00169",cytosol,Day),
  catalyst(10402,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00117",cytosol,Day) :-
  not exclude(10411),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C04332",cytosol,Day),
  catalyst(10411,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04454",cytosol,Day) :-
  not exclude(10411),
  Day >= 1,
  in_compartment(Experiment,"C00009",cytosol,Day),
  in_compartment(Experiment,"C04332",cytosol,Day),
  catalyst(10411,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00009",cytosol,Day) :-
  not exclude(10412),
  Day >= 1,
  in_compartment(Experiment,"C00117",cytosol,Day),
  in_compartment(Experiment,"C04454",cytosol,Day),
  catalyst(10412,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04332",cytosol,Day) :-
  not exclude(10412),
  Day >= 1,
  in_compartment(Experiment,"C00117",cytosol,Day),
  in_compartment(Experiment,"C04454",cytosol,Day),
  catalyst(10412,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00255",cytosol,Day) :-
  not exclude(10421),
  Day >= 1,
  in_compartment(Experiment,"C04332",cytosol,Day),
  catalyst(10421,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04732",cytosol,Day) :-
  not exclude(10421),
  Day >= 1,
  in_compartment(Experiment,"C04332",cytosol,Day),
  catalyst(10421,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04332",cytosol,Day) :-
  not exclude(10422),
  Day >= 1,
  in_compartment(Experiment,"C00255",cytosol,Day),
  in_compartment(Experiment,"C04732",cytosol,Day),
  catalyst(10422,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(10441),
  Day >= 1,
  in_compartment(Experiment,"C00091",cytosol,Day),
  in_compartment(Experiment,"C00579",cytosol,Day),
  catalyst(10441,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01169",cytosol,Day) :-
  not exclude(10441),
  Day >= 1,
  in_compartment(Experiment,"C00091",cytosol,Day),
  in_compartment(Experiment,"C00579",cytosol,Day),
  catalyst(10441,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00091",cytosol,Day) :-
  not exclude(10442),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C01169",cytosol,Day),
  catalyst(10442,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00579",cytosol,Day) :-
  not exclude(10442),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C01169",cytosol,Day),
  catalyst(10442,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(10451),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05761",cytosol,Day),
  catalyst(10451,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(10451),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05761",cytosol,Day),
  catalyst(10451,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05762",cytosol,Day) :-
  not exclude(10451),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05761",cytosol,Day),
  catalyst(10451,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01209",cytosol,Day) :-
  not exclude(10452),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00229",cytosol,Day),
  in_compartment(Experiment,"C05762",cytosol,Day),
  catalyst(10452,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05761",cytosol,Day) :-
  not exclude(10452),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00229",cytosol,Day),
  in_compartment(Experiment,"C05762",cytosol,Day),
  catalyst(10452,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(10461),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05755",cytosol,Day),
  catalyst(10461,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(10461),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05755",cytosol,Day),
  catalyst(10461,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05756",cytosol,Day) :-
  not exclude(10461),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05755",cytosol,Day),
  catalyst(10461,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01209",cytosol,Day) :-
  not exclude(10462),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00229",cytosol,Day),
  in_compartment(Experiment,"C05756",cytosol,Day),
  catalyst(10462,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05755",cytosol,Day) :-
  not exclude(10462),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00229",cytosol,Day),
  in_compartment(Experiment,"C05756",cytosol,Day),
  catalyst(10462,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(10481),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05749",cytosol,Day),
  catalyst(10481,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(10481),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05749",cytosol,Day),
  catalyst(10481,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05750",cytosol,Day) :-
  not exclude(10481),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05749",cytosol,Day),
  catalyst(10481,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01209",cytosol,Day) :-
  not exclude(10482),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00229",cytosol,Day),
  in_compartment(Experiment,"C05750",cytosol,Day),
  catalyst(10482,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05749",cytosol,Day) :-
  not exclude(10482),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00229",cytosol,Day),
  in_compartment(Experiment,"C05750",cytosol,Day),
  catalyst(10482,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(10491),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05745",cytosol,Day),
  catalyst(10491,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(10491),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05745",cytosol,Day),
  catalyst(10491,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05746",cytosol,Day) :-
  not exclude(10491),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05745",cytosol,Day),
  catalyst(10491,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01209",cytosol,Day) :-
  not exclude(10492),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00229",cytosol,Day),
  in_compartment(Experiment,"C05746",cytosol,Day),
  catalyst(10492,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05745",cytosol,Day) :-
  not exclude(10492),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00229",cytosol,Day),
  in_compartment(Experiment,"C05746",cytosol,Day),
  catalyst(10492,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(10501),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05223",cytosol,Day),
  catalyst(10501,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(10501),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05223",cytosol,Day),
  catalyst(10501,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05759",cytosol,Day) :-
  not exclude(10501),
  Day >= 1,
  in_compartment(Experiment,"C01209",cytosol,Day),
  in_compartment(Experiment,"C05223",cytosol,Day),
  catalyst(10501,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01209",cytosol,Day) :-
  not exclude(10502),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00229",cytosol,Day),
  in_compartment(Experiment,"C05759",cytosol,Day),
  catalyst(10502,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05223",cytosol,Day) :-
  not exclude(10502),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00229",cytosol,Day),
  in_compartment(Experiment,"C05759",cytosol,Day),
  catalyst(10502,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(10521),
  Day >= 1,
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(10521,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(10521),
  Day >= 1,
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(10521,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00685",cytosol,Day) :-
  not exclude(10521),
  Day >= 1,
  in_compartment(Experiment,"C00173",cytosol,Day),
  in_compartment(Experiment,"C01209",cytosol,Day),
  catalyst(10521,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00173",cytosol,Day) :-
  not exclude(10522),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00229",cytosol,Day),
  in_compartment(Experiment,"C00685",cytosol,Day),
  catalyst(10522,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01209",cytosol,Day) :-
  not exclude(10522),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00229",cytosol,Day),
  in_compartment(Experiment,"C00685",cytosol,Day),
  catalyst(10522,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(10541),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00579",cytosol,Day),
  catalyst(10541,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01136",cytosol,Day) :-
  not exclude(10541),
  Day >= 1,
  in_compartment(Experiment,"C00024",cytosol,Day),
  in_compartment(Experiment,"C00579",cytosol,Day),
  catalyst(10541,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00024",cytosol,Day) :-
  not exclude(10542),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C01136",cytosol,Day),
  catalyst(10542,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00579",cytosol,Day) :-
  not exclude(10542),
  Day >= 1,
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C01136",cytosol,Day),
  catalyst(10542,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(10561),
  Day >= 1,
  in_compartment(Experiment,"C00068",cytosol,Day),
  in_compartment(Experiment,"C06010",cytosol,Day),
  catalyst(10561,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05125",cytosol,Day) :-
  not exclude(10561),
  Day >= 1,
  in_compartment(Experiment,"C00068",cytosol,Day),
  in_compartment(Experiment,"C06010",cytosol,Day),
  catalyst(10561,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00068",cytosol,Day) :-
  not exclude(10562),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  in_compartment(Experiment,"C05125",cytosol,Day),
  catalyst(10562,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C06010",cytosol,Day) :-
  not exclude(10562),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  in_compartment(Experiment,"C05125",cytosol,Day),
  catalyst(10562,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(10581),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C06010",cytosol,Day),
  catalyst(10581,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(10582),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(10582,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C06010",cytosol,Day) :-
  not exclude(10582),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(10582,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(10591),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00900",cytosol,Day),
  catalyst(10591,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(10592),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(10592,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00900",cytosol,Day) :-
  not exclude(10592),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(10592,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00342",cytosol,Day) :-
  not exclude(10601),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00343",cytosol,Day),
  in_compartment(Experiment,"C04232",cytosol,Day),
  catalyst(10601,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C03723",cytosol,Day) :-
  not exclude(10601),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00343",cytosol,Day),
  in_compartment(Experiment,"C04232",cytosol,Day),
  catalyst(10601,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(10602),
  Day >= 1,
  in_compartment(Experiment,"C00342",cytosol,Day),
  in_compartment(Experiment,"C03723",cytosol,Day),
  catalyst(10602,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00343",cytosol,Day) :-
  not exclude(10602),
  Day >= 1,
  in_compartment(Experiment,"C00342",cytosol,Day),
  in_compartment(Experiment,"C03723",cytosol,Day),
  catalyst(10602,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04232",cytosol,Day) :-
  not exclude(10602),
  Day >= 1,
  in_compartment(Experiment,"C00342",cytosol,Day),
  in_compartment(Experiment,"C03723",cytosol,Day),
  catalyst(10602,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00112",cytosol,Day) :-
  not exclude(10611),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00343",cytosol,Day),
  in_compartment(Experiment,"C00705",cytosol,Day),
  catalyst(10611,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00342",cytosol,Day) :-
  not exclude(10611),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00343",cytosol,Day),
  in_compartment(Experiment,"C00705",cytosol,Day),
  catalyst(10611,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(10612),
  Day >= 1,
  in_compartment(Experiment,"C00112",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(10612,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00343",cytosol,Day) :-
  not exclude(10612),
  Day >= 1,
  in_compartment(Experiment,"C00112",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(10612,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00705",cytosol,Day) :-
  not exclude(10612),
  Day >= 1,
  in_compartment(Experiment,"C00112",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(10612,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00035",cytosol,Day) :-
  not exclude(10621),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00343",cytosol,Day),
  in_compartment(Experiment,"C00361",cytosol,Day),
  catalyst(10621,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00342",cytosol,Day) :-
  not exclude(10621),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00343",cytosol,Day),
  in_compartment(Experiment,"C00361",cytosol,Day),
  catalyst(10621,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(10622),
  Day >= 1,
  in_compartment(Experiment,"C00035",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(10622,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00343",cytosol,Day) :-
  not exclude(10622),
  Day >= 1,
  in_compartment(Experiment,"C00035",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(10622,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00361",cytosol,Day) :-
  not exclude(10622),
  Day >= 1,
  in_compartment(Experiment,"C00035",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(10622,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(10641),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00206",cytosol,Day),
  in_compartment(Experiment,"C00343",cytosol,Day),
  catalyst(10641,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00342",cytosol,Day) :-
  not exclude(10641),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00206",cytosol,Day),
  in_compartment(Experiment,"C00343",cytosol,Day),
  catalyst(10641,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(10642),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(10642,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00206",cytosol,Day) :-
  not exclude(10642),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(10642,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00343",cytosol,Day) :-
  not exclude(10642),
  Day >= 1,
  in_compartment(Experiment,"C00008",cytosol,Day),
  in_compartment(Experiment,"C00342",cytosol,Day),
  catalyst(10642,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00126",cytosol,Day) :-
  not exclude(10651),
  Day >= 1,
  in_compartment(Experiment,"C00125",cytosol,Day),
  in_compartment(Experiment,"C00390",cytosol,Day),
  catalyst(10651,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00399",cytosol,Day) :-
  not exclude(10651),
  Day >= 1,
  in_compartment(Experiment,"C00125",cytosol,Day),
  in_compartment(Experiment,"C00390",cytosol,Day),
  catalyst(10651,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00125",cytosol,Day) :-
  not exclude(10652),
  Day >= 1,
  in_compartment(Experiment,"C00126",cytosol,Day),
  in_compartment(Experiment,"C00399",cytosol,Day),
  catalyst(10652,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00390",cytosol,Day) :-
  not exclude(10652),
  Day >= 1,
  in_compartment(Experiment,"C00126",cytosol,Day),
  in_compartment(Experiment,"C00399",cytosol,Day),
  catalyst(10652,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(10661),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00126",cytosol,Day),
  catalyst(10661,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00125",cytosol,Day) :-
  not exclude(10661),
  Day >= 1,
  in_compartment(Experiment,"C00007",cytosol,Day),
  in_compartment(Experiment,"C00126",cytosol,Day),
  catalyst(10661,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",cytosol,Day) :-
  not exclude(10662),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00125",cytosol,Day),
  catalyst(10662,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00126",cytosol,Day) :-
  not exclude(10662),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00125",cytosol,Day),
  catalyst(10662,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00068",cytosol,Day) :-
  not exclude(10681),
  Day >= 1,
  in_compartment(Experiment,"C00248",cytosol,Day),
  in_compartment(Experiment,"C05125",cytosol,Day),
  catalyst(10681,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01136",cytosol,Day) :-
  not exclude(10681),
  Day >= 1,
  in_compartment(Experiment,"C00248",cytosol,Day),
  in_compartment(Experiment,"C05125",cytosol,Day),
  catalyst(10681,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00248",cytosol,Day) :-
  not exclude(10682),
  Day >= 1,
  in_compartment(Experiment,"C00068",cytosol,Day),
  in_compartment(Experiment,"C01136",cytosol,Day),
  catalyst(10682,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05125",cytosol,Day) :-
  not exclude(10682),
  Day >= 1,
  in_compartment(Experiment,"C00068",cytosol,Day),
  in_compartment(Experiment,"C01136",cytosol,Day),
  catalyst(10682,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(10691),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  in_compartment(Experiment,"C00248",cytosol,Day),
  catalyst(10691,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01136",cytosol,Day) :-
  not exclude(10691),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  in_compartment(Experiment,"C00248",cytosol,Day),
  catalyst(10691,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(10692),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C01136",cytosol,Day),
  catalyst(10692,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00248",cytosol,Day) :-
  not exclude(10692),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C01136",cytosol,Day),
  catalyst(10692,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10701),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(10701,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(10701),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(10701,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00024",cytosol,Day) :-
  not exclude(10701),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(10701,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10702),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00024",cytosol,Day),
  catalyst(10702,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(10702),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00024",cytosol,Day),
  catalyst(10702,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(10702),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00024",cytosol,Day),
  catalyst(10702,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(10711),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(10711,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(10711),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(10711,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00024",cytosol,Day) :-
  not exclude(10711),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00010",cytosol,Day),
  in_compartment(Experiment,"C00022",cytosol,Day),
  catalyst(10711,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(10712),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00024",cytosol,Day),
  catalyst(10712,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00010",cytosol,Day) :-
  not exclude(10712),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00024",cytosol,Day),
  catalyst(10712,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(10712),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00024",cytosol,Day),
  catalyst(10712,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00022",cytosol,Day) :-
  not exclude(10721),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C05125",cytosol,Day),
  catalyst(10721,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00068",cytosol,Day) :-
  not exclude(10721),
  Day >= 1,
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C05125",cytosol,Day),
  catalyst(10721,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(10722),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  in_compartment(Experiment,"C00068",cytosol,Day),
  catalyst(10722,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05125",cytosol,Day) :-
  not exclude(10722),
  Day >= 1,
  in_compartment(Experiment,"C00022",cytosol,Day),
  in_compartment(Experiment,"C00068",cytosol,Day),
  catalyst(10722,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10741),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C05535",cytosol,Day),
  catalyst(10741,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04076",cytosol,Day) :-
  not exclude(10741),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C05535",cytosol,Day),
  catalyst(10741,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C11482",cytosol,Day) :-
  not exclude(10741),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C05535",cytosol,Day),
  catalyst(10741,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10742),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C04076",cytosol,Day),
  in_compartment(Experiment,"C11482",cytosol,Day),
  catalyst(10742,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10742),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C04076",cytosol,Day),
  in_compartment(Experiment,"C11482",cytosol,Day),
  catalyst(10742,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05535",cytosol,Day) :-
  not exclude(10742),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C04076",cytosol,Day),
  in_compartment(Experiment,"C11482",cytosol,Day),
  catalyst(10742,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(10761),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C04076",cytosol,Day),
  catalyst(10761,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10761),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C04076",cytosol,Day),
  catalyst(10761,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00956",cytosol,Day) :-
  not exclude(10761),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C04076",cytosol,Day),
  catalyst(10761,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(10762),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00956",cytosol,Day),
  catalyst(10762,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(10762),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00956",cytosol,Day),
  catalyst(10762,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04076",cytosol,Day) :-
  not exclude(10762),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  in_compartment(Experiment,"C00956",cytosol,Day),
  catalyst(10762,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10781),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C05757",cytosol,Day),
  catalyst(10781,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05756",cytosol,Day) :-
  not exclude(10781),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C05757",cytosol,Day),
  catalyst(10781,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10782),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C05756",cytosol,Day),
  catalyst(10782,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05757",cytosol,Day) :-
  not exclude(10782),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C05756",cytosol,Day),
  catalyst(10782,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10791),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C05747",cytosol,Day),
  catalyst(10791,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05746",cytosol,Day) :-
  not exclude(10791),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C05747",cytosol,Day),
  catalyst(10791,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10792),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C05746",cytosol,Day),
  catalyst(10792,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05747",cytosol,Day) :-
  not exclude(10792),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C05746",cytosol,Day),
  catalyst(10792,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10811),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C04633",cytosol,Day),
  catalyst(10811,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05762",cytosol,Day) :-
  not exclude(10811),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C04633",cytosol,Day),
  catalyst(10811,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10812),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C05762",cytosol,Day),
  catalyst(10812,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04633",cytosol,Day) :-
  not exclude(10812),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C05762",cytosol,Day),
  catalyst(10812,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10821),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C04620",cytosol,Day),
  catalyst(10821,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05750",cytosol,Day) :-
  not exclude(10821),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C04620",cytosol,Day),
  catalyst(10821,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10822),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C05750",cytosol,Day),
  catalyst(10822,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04620",cytosol,Day) :-
  not exclude(10822),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C05750",cytosol,Day),
  catalyst(10822,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10831),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C04619",cytosol,Day),
  catalyst(10831,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05753",cytosol,Day) :-
  not exclude(10831),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C04619",cytosol,Day),
  catalyst(10831,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10832),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C05753",cytosol,Day),
  catalyst(10832,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04619",cytosol,Day) :-
  not exclude(10832),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C05753",cytosol,Day),
  catalyst(10832,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(10841),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C04618",cytosol,Day),
  catalyst(10841,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05744",cytosol,Day) :-
  not exclude(10841),
  Day >= 1,
  in_compartment(Experiment,"C00006",cytosol,Day),
  in_compartment(Experiment,"C04618",cytosol,Day),
  catalyst(10841,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(10842),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C05744",cytosol,Day),
  catalyst(10842,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C04618",cytosol,Day) :-
  not exclude(10842),
  Day >= 1,
  in_compartment(Experiment,"C00005",cytosol,Day),
  in_compartment(Experiment,"C05744",cytosol,Day),
  catalyst(10842,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(10861),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00311",cytosol,Day),
  catalyst(10861,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00011",cytosol,Day) :-
  not exclude(10861),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00311",cytosol,Day),
  catalyst(10861,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00026",cytosol,Day) :-
  not exclude(10861),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00311",cytosol,Day),
  catalyst(10861,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00080",cytosol,Day) :-
  not exclude(10861),
  Day >= 1,
  in_compartment(Experiment,"C00003",cytosol,Day),
  in_compartment(Experiment,"C00311",cytosol,Day),
  catalyst(10861,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(10862),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  catalyst(10862,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00311",cytosol,Day) :-
  not exclude(10862),
  Day >= 1,
  in_compartment(Experiment,"C00004",cytosol,Day),
  in_compartment(Experiment,"C00011",cytosol,Day),
  in_compartment(Experiment,"C00026",cytosol,Day),
  in_compartment(Experiment,"C00080",cytosol,Day),
  catalyst(10862,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00229",cytosol,Day) :-
  not exclude(10871),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C05764",cytosol,Day),
  catalyst(10871,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00249",cytosol,Day) :-
  not exclude(10871),
  Day >= 1,
  in_compartment(Experiment,"C00001",cytosol,Day),
  in_compartment(Experiment,"C05764",cytosol,Day),
  catalyst(10871,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(10872),
  Day >= 1,
  in_compartment(Experiment,"C00229",cytosol,Day),
  in_compartment(Experiment,"C00249",cytosol,Day),
  catalyst(10872,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C05764",cytosol,Day) :-
  not exclude(10872),
  Day >= 1,
  in_compartment(Experiment,"C00229",cytosol,Day),
  in_compartment(Experiment,"C00249",cytosol,Day),
  catalyst(10872,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00463",cytosol,Day) :-
  include(10900),
  Day >= 1,
  in_compartment(Experiment,"C03506",cytosol,Day),
  catalyst(10900,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00661",cytosol,Day) :-
  include(10900),
  Day >= 1,
  in_compartment(Experiment,"C03506",cytosol,Day),
  catalyst(10900,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  include(10910),
  Day >= 1,
  in_compartment(Experiment,"C00065",cytosol,Day),
  in_compartment(Experiment,"C00463",cytosol,Day),
  catalyst(10910,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00078",cytosol,Day) :-
  include(10910),
  Day >= 1,
  in_compartment(Experiment,"C00065",cytosol,Day),
  in_compartment(Experiment,"C00463",cytosol,Day),
  catalyst(10910,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00463",cytosol,Day) :-
  not exclude(10920),
  Day >= 1,
  in_compartment(Experiment,"C00463",medium,Day),
  catalyst(10920,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00074",cytosol,Day) :-
  not exclude(30010),
  Day >= 1,
  in_compartment(Experiment,"C00074",medium,Day),
  catalyst(30010,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00108",cytosol,Day) :-
  not exclude(30020),
  Day >= 1,
  in_compartment(Experiment,"C00108",medium,Day),
  catalyst(30020,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00166",cytosol,Day) :-
  not exclude(30030),
  Day >= 1,
  in_compartment(Experiment,"C00166",medium,Day),
  catalyst(30030,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00493",cytosol,Day) :-
  not exclude(30040),
  Day >= 1,
  in_compartment(Experiment,"C00493",medium,Day),
  catalyst(30040,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C01179",cytosol,Day) :-
  not exclude(30050),
  Day >= 1,
  in_compartment(Experiment,"C01179",medium,Day),
  catalyst(30050,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00279",cytosol,Day) :-
  not exclude(30060),
  Day >= 1,
  in_compartment(Experiment,"C00279",medium,Day),
  catalyst(30060,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00631",cytosol,Day) :-
  not exclude(30070),
  Day >= 1,
  in_compartment(Experiment,"C00631",medium,Day),
  catalyst(30070,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00001",cytosol,Day) :-
  not exclude(30080),
  Day >= 1,
  in_compartment(Experiment,"C00001",medium,Day),
  catalyst(30080,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00002",cytosol,Day) :-
  not exclude(30090),
  Day >= 1,
  in_compartment(Experiment,"C00002",medium,Day),
  catalyst(30090,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00003",cytosol,Day) :-
  not exclude(30100),
  Day >= 1,
  in_compartment(Experiment,"C00003",medium,Day),
  catalyst(30100,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00004",cytosol,Day) :-
  not exclude(30110),
  Day >= 1,
  in_compartment(Experiment,"C00004",medium,Day),
  catalyst(30110,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00005",cytosol,Day) :-
  not exclude(30120),
  Day >= 1,
  in_compartment(Experiment,"C00005",medium,Day),
  catalyst(30120,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00006",cytosol,Day) :-
  not exclude(30130),
  Day >= 1,
  in_compartment(Experiment,"C00006",medium,Day),
  catalyst(30130,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00007",cytosol,Day) :-
  not exclude(30140),
  Day >= 1,
  in_compartment(Experiment,"C00007",medium,Day),
  catalyst(30140,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00008",cytosol,Day) :-
  not exclude(30150),
  Day >= 1,
  in_compartment(Experiment,"C00008",medium,Day),
  catalyst(30150,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

in_compartment(Experiment,"C00119",cytosol,Day) :-
  not exclude(30160),
  Day >= 1,
  in_compartment(Experiment,"C00119",medium,Day),
  catalyst(30160,Complex),
  not inhibited(Experiment,Complex,Day),
  not deleted(Experiment,Complex).

assertable_reaction(10900).
assertable_reaction(10910).

retractable_reaction(10).
retractable_reaction(21).
retractable_reaction(22).
retractable_reaction(31).
retractable_reaction(32).
retractable_reaction(41).
retractable_reaction(42).
retractable_reaction(51).
retractable_reaction(52).
retractable_reaction(91).
retractable_reaction(92).
retractable_reaction(101).
retractable_reaction(102).
retractable_reaction(111).
retractable_reaction(112).
retractable_reaction(131).
retractable_reaction(132).
retractable_reaction(141).
retractable_reaction(142).
retractable_reaction(151).
retractable_reaction(152).
retractable_reaction(190).
retractable_reaction(230).
retractable_reaction(241).
retractable_reaction(242).
retractable_reaction(251).
retractable_reaction(252).
retractable_reaction(261).
retractable_reaction(262).
retractable_reaction(321).
retractable_reaction(322).
retractable_reaction(341).
retractable_reaction(342).
retractable_reaction(350).
retractable_reaction(361).
retractable_reaction(362).
retractable_reaction(371).
retractable_reaction(372).
retractable_reaction(390).
retractable_reaction(401).
retractable_reaction(402).
retractable_reaction(451).
retractable_reaction(452).
retractable_reaction(460).
retractable_reaction(490).
retractable_reaction(510).
retractable_reaction(530).
retractable_reaction(540).
retractable_reaction(550).
retractable_reaction(560).
retractable_reaction(581).
retractable_reaction(582).
retractable_reaction(590).
retractable_reaction(600).
retractable_reaction(630).
retractable_reaction(650).
retractable_reaction(670).
retractable_reaction(690).
retractable_reaction(730).
retractable_reaction(750).
retractable_reaction(781).
retractable_reaction(782).
retractable_reaction(791).
retractable_reaction(792).
retractable_reaction(801).
retractable_reaction(802).
retractable_reaction(811).
retractable_reaction(812).
retractable_reaction(821).
retractable_reaction(822).
retractable_reaction(831).
retractable_reaction(832).
retractable_reaction(841).
retractable_reaction(842).
retractable_reaction(861).
retractable_reaction(862).
retractable_reaction(871).
retractable_reaction(872).
retractable_reaction(881).
retractable_reaction(882).
retractable_reaction(901).
retractable_reaction(902).
retractable_reaction(911).
retractable_reaction(912).
retractable_reaction(921).
retractable_reaction(922).
retractable_reaction(931).
retractable_reaction(932).
retractable_reaction(941).
retractable_reaction(942).
retractable_reaction(970).
retractable_reaction(980).
retractable_reaction(990).
retractable_reaction(1000).
retractable_reaction(1010).
retractable_reaction(1021).
retractable_reaction(1022).
retractable_reaction(1041).
retractable_reaction(1042).
retractable_reaction(1050).
retractable_reaction(1111).
retractable_reaction(1112).
retractable_reaction(1121).
retractable_reaction(1122).
retractable_reaction(1130).
retractable_reaction(1140).
retractable_reaction(1150).
retractable_reaction(1160).
retractable_reaction(1191).
retractable_reaction(1192).
retractable_reaction(1200).
retractable_reaction(1220).
retractable_reaction(1250).
retractable_reaction(1261).
retractable_reaction(1262).
retractable_reaction(1291).
retractable_reaction(1292).
retractable_reaction(1301).
retractable_reaction(1302).
retractable_reaction(1311).
retractable_reaction(1312).
retractable_reaction(1321).
retractable_reaction(1322).
retractable_reaction(1331).
retractable_reaction(1332).
retractable_reaction(1341).
retractable_reaction(1342).
retractable_reaction(1351).
retractable_reaction(1352).
retractable_reaction(1371).
retractable_reaction(1372).
retractable_reaction(1381).
retractable_reaction(1382).
retractable_reaction(1411).
retractable_reaction(1412).
retractable_reaction(1431).
retractable_reaction(1432).
retractable_reaction(1451).
retractable_reaction(1452).
retractable_reaction(1491).
retractable_reaction(1492).
retractable_reaction(1501).
retractable_reaction(1502).
retractable_reaction(1511).
retractable_reaction(1512).
retractable_reaction(1521).
retractable_reaction(1522).
retractable_reaction(1531).
retractable_reaction(1532).
retractable_reaction(1540).
retractable_reaction(1561).
retractable_reaction(1562).
retractable_reaction(1571).
retractable_reaction(1572).
retractable_reaction(1581).
retractable_reaction(1582).
retractable_reaction(1590).
retractable_reaction(1611).
retractable_reaction(1612).
retractable_reaction(1641).
retractable_reaction(1642).
retractable_reaction(1671).
retractable_reaction(1672).
retractable_reaction(1681).
retractable_reaction(1682).
retractable_reaction(1691).
retractable_reaction(1692).
retractable_reaction(1701).
retractable_reaction(1702).
retractable_reaction(1721).
retractable_reaction(1722).
retractable_reaction(1731).
retractable_reaction(1732).
retractable_reaction(1741).
retractable_reaction(1742).
retractable_reaction(1751).
retractable_reaction(1752).
retractable_reaction(1771).
retractable_reaction(1772).
retractable_reaction(1781).
retractable_reaction(1782).
retractable_reaction(1791).
retractable_reaction(1792).
retractable_reaction(1801).
retractable_reaction(1802).
retractable_reaction(1810).
retractable_reaction(1820).
retractable_reaction(1840).
retractable_reaction(1850).
retractable_reaction(1860).
retractable_reaction(1870).
retractable_reaction(1880).
retractable_reaction(1890).
retractable_reaction(1900).
retractable_reaction(1910).
retractable_reaction(1920).
retractable_reaction(1940).
retractable_reaction(1950).
retractable_reaction(1960).
retractable_reaction(1970).
retractable_reaction(2000).
retractable_reaction(2020).
retractable_reaction(2031).
retractable_reaction(2032).
retractable_reaction(2041).
retractable_reaction(2042).
retractable_reaction(2051).
retractable_reaction(2052).
retractable_reaction(2060).
retractable_reaction(2070).
retractable_reaction(2090).
retractable_reaction(2100).
retractable_reaction(2110).
retractable_reaction(2121).
retractable_reaction(2122).
retractable_reaction(2131).
retractable_reaction(2132).
retractable_reaction(2140).
retractable_reaction(2150).
retractable_reaction(2160).
retractable_reaction(2170).
retractable_reaction(2180).
retractable_reaction(2190).
retractable_reaction(2200).
retractable_reaction(2210).
retractable_reaction(2220).
retractable_reaction(2231).
retractable_reaction(2232).
retractable_reaction(2240).
retractable_reaction(2270).
retractable_reaction(2280).
retractable_reaction(2290).
retractable_reaction(2300).
retractable_reaction(2320).
retractable_reaction(2330).
retractable_reaction(2340).
retractable_reaction(2350).
retractable_reaction(2370).
retractable_reaction(2380).
retractable_reaction(2391).
retractable_reaction(2392).
retractable_reaction(2401).
retractable_reaction(2402).
retractable_reaction(2410).
retractable_reaction(2431).
retractable_reaction(2432).
retractable_reaction(2441).
retractable_reaction(2442).
retractable_reaction(2450).
retractable_reaction(2461).
retractable_reaction(2462).
retractable_reaction(2480).
retractable_reaction(2490).
retractable_reaction(2500).
retractable_reaction(2510).
retractable_reaction(2520).
retractable_reaction(2530).
retractable_reaction(2540).
retractable_reaction(2550).
retractable_reaction(2560).
retractable_reaction(2580).
retractable_reaction(2590).
retractable_reaction(2621).
retractable_reaction(2622).
retractable_reaction(2631).
retractable_reaction(2632).
retractable_reaction(2641).
retractable_reaction(2642).
retractable_reaction(2651).
retractable_reaction(2652).
retractable_reaction(2660).
retractable_reaction(2670).
retractable_reaction(2691).
retractable_reaction(2692).
retractable_reaction(2711).
retractable_reaction(2712).
retractable_reaction(2721).
retractable_reaction(2722).
retractable_reaction(2731).
retractable_reaction(2732).
retractable_reaction(2740).
retractable_reaction(2750).
retractable_reaction(2760).
retractable_reaction(2780).
retractable_reaction(2790).
retractable_reaction(2800).
retractable_reaction(2820).
retractable_reaction(2830).
retractable_reaction(2840).
retractable_reaction(2860).
retractable_reaction(2891).
retractable_reaction(2892).
retractable_reaction(2910).
retractable_reaction(2920).
retractable_reaction(2940).
retractable_reaction(2950).
retractable_reaction(2960).
retractable_reaction(2970).
retractable_reaction(2980).
retractable_reaction(2990).
retractable_reaction(3000).
retractable_reaction(3010).
retractable_reaction(3020).
retractable_reaction(3030).
retractable_reaction(3040).
retractable_reaction(3050).
retractable_reaction(3070).
retractable_reaction(3090).
retractable_reaction(3120).
retractable_reaction(3130).
retractable_reaction(3141).
retractable_reaction(3142).
retractable_reaction(3160).
retractable_reaction(3180).
retractable_reaction(3211).
retractable_reaction(3212).
retractable_reaction(3220).
retractable_reaction(3230).
retractable_reaction(3281).
retractable_reaction(3282).
retractable_reaction(3290).
retractable_reaction(3300).
retractable_reaction(3310).
retractable_reaction(3320).
retractable_reaction(3330).
retractable_reaction(3350).
retractable_reaction(3370).
retractable_reaction(3390).
retractable_reaction(3420).
retractable_reaction(3430).
retractable_reaction(3440).
retractable_reaction(3450).
retractable_reaction(3480).
retractable_reaction(3490).
retractable_reaction(3500).
retractable_reaction(3510).
retractable_reaction(3520).
retractable_reaction(3540).
retractable_reaction(3550).
retractable_reaction(3571).
retractable_reaction(3572).
retractable_reaction(3590).
retractable_reaction(3600).
retractable_reaction(3610).
retractable_reaction(3620).
retractable_reaction(3630).
retractable_reaction(3650).
retractable_reaction(3660).
retractable_reaction(3671).
retractable_reaction(3672).
retractable_reaction(3680).
retractable_reaction(3690).
retractable_reaction(3700).
retractable_reaction(3710).
retractable_reaction(3720).
retractable_reaction(3730).
retractable_reaction(3740).
retractable_reaction(3750).
retractable_reaction(3760).
retractable_reaction(3770).
retractable_reaction(3780).
retractable_reaction(3800).
retractable_reaction(3810).
retractable_reaction(3850).
retractable_reaction(3860).
retractable_reaction(3880).
retractable_reaction(3890).
retractable_reaction(3900).
retractable_reaction(3930).
retractable_reaction(3941).
retractable_reaction(3942).
retractable_reaction(3950).
retractable_reaction(3961).
retractable_reaction(3962).
retractable_reaction(3971).
retractable_reaction(3972).
retractable_reaction(3980).
retractable_reaction(3990).
retractable_reaction(4000).
retractable_reaction(4020).
retractable_reaction(4030).
retractable_reaction(4050).
retractable_reaction(4060).
retractable_reaction(4070).
retractable_reaction(4100).
retractable_reaction(4121).
retractable_reaction(4122).
retractable_reaction(4131).
retractable_reaction(4132).
retractable_reaction(4170).
retractable_reaction(4191).
retractable_reaction(4192).
retractable_reaction(4250).
retractable_reaction(4260).
retractable_reaction(4271).
retractable_reaction(4272).
retractable_reaction(4281).
retractable_reaction(4282).
retractable_reaction(4291).
retractable_reaction(4292).
retractable_reaction(4301).
retractable_reaction(4302).
retractable_reaction(4311).
retractable_reaction(4312).
retractable_reaction(4330).
retractable_reaction(4340).
retractable_reaction(4350).
retractable_reaction(4360).
retractable_reaction(4371).
retractable_reaction(4372).
retractable_reaction(4380).
retractable_reaction(4390).
retractable_reaction(4400).
retractable_reaction(4410).
retractable_reaction(4421).
retractable_reaction(4422).
retractable_reaction(4430).
retractable_reaction(4451).
retractable_reaction(4452).
retractable_reaction(4470).
retractable_reaction(4480).
retractable_reaction(4490).
retractable_reaction(4500).
retractable_reaction(4510).
retractable_reaction(4520).
retractable_reaction(4540).
retractable_reaction(4551).
retractable_reaction(4552).
retractable_reaction(4560).
retractable_reaction(4570).
retractable_reaction(4580).
retractable_reaction(4590).
retractable_reaction(4600).
retractable_reaction(4620).
retractable_reaction(4630).
retractable_reaction(4640).
retractable_reaction(4681).
retractable_reaction(4682).
retractable_reaction(4690).
retractable_reaction(4700).
retractable_reaction(4710).
retractable_reaction(4720).
retractable_reaction(4730).
retractable_reaction(4750).
retractable_reaction(4760).
retractable_reaction(4781).
retractable_reaction(4782).
retractable_reaction(4840).
retractable_reaction(4850).
retractable_reaction(4870).
retractable_reaction(4880).
retractable_reaction(4891).
retractable_reaction(4892).
retractable_reaction(4900).
retractable_reaction(4910).
retractable_reaction(4920).
retractable_reaction(4940).
retractable_reaction(4960).
retractable_reaction(4971).
retractable_reaction(4972).
retractable_reaction(4981).
retractable_reaction(4982).
retractable_reaction(4991).
retractable_reaction(4992).
retractable_reaction(5000).
retractable_reaction(5010).
retractable_reaction(5020).
retractable_reaction(5030).
retractable_reaction(5050).
retractable_reaction(5060).
retractable_reaction(5080).
retractable_reaction(5090).
retractable_reaction(5100).
retractable_reaction(5110).
retractable_reaction(5120).
retractable_reaction(5140).
retractable_reaction(5150).
retractable_reaction(5160).
retractable_reaction(5170).
retractable_reaction(5190).
retractable_reaction(5200).
retractable_reaction(5210).
retractable_reaction(5220).
retractable_reaction(5230).
retractable_reaction(5250).
retractable_reaction(5260).
retractable_reaction(5301).
retractable_reaction(5302).
retractable_reaction(5310).
retractable_reaction(5330).
retractable_reaction(5340).
retractable_reaction(5350).
retractable_reaction(5361).
retractable_reaction(5362).
retractable_reaction(5371).
retractable_reaction(5372).
retractable_reaction(5381).
retractable_reaction(5382).
retractable_reaction(5391).
retractable_reaction(5392).
retractable_reaction(5401).
retractable_reaction(5402).
retractable_reaction(5411).
retractable_reaction(5412).
retractable_reaction(5421).
retractable_reaction(5422).
retractable_reaction(5431).
retractable_reaction(5432).
retractable_reaction(5451).
retractable_reaction(5452).
retractable_reaction(5471).
retractable_reaction(5472).
retractable_reaction(5481).
retractable_reaction(5482).
retractable_reaction(5491).
retractable_reaction(5492).
retractable_reaction(5511).
retractable_reaction(5512).
retractable_reaction(5520).
retractable_reaction(5540).
retractable_reaction(5550).
retractable_reaction(5561).
retractable_reaction(5562).
retractable_reaction(5581).
retractable_reaction(5582).
retractable_reaction(5591).
retractable_reaction(5592).
retractable_reaction(5601).
retractable_reaction(5602).
retractable_reaction(5611).
retractable_reaction(5612).
retractable_reaction(5621).
retractable_reaction(5622).
retractable_reaction(5630).
retractable_reaction(5640).
retractable_reaction(5661).
retractable_reaction(5662).
retractable_reaction(5691).
retractable_reaction(5692).
retractable_reaction(5701).
retractable_reaction(5702).
retractable_reaction(5711).
retractable_reaction(5712).
retractable_reaction(5730).
retractable_reaction(5750).
retractable_reaction(5770).
retractable_reaction(5780).
retractable_reaction(5801).
retractable_reaction(5802).
retractable_reaction(5830).
retractable_reaction(5840).
retractable_reaction(5880).
retractable_reaction(5911).
retractable_reaction(5912).
retractable_reaction(5921).
retractable_reaction(5922).
retractable_reaction(5930).
retractable_reaction(5940).
retractable_reaction(5960).
retractable_reaction(5970).
retractable_reaction(5990).
retractable_reaction(6010).
retractable_reaction(6020).
retractable_reaction(6030).
retractable_reaction(6040).
retractable_reaction(6051).
retractable_reaction(6052).
retractable_reaction(6071).
retractable_reaction(6072).
retractable_reaction(6081).
retractable_reaction(6082).
retractable_reaction(6091).
retractable_reaction(6092).
retractable_reaction(6120).
retractable_reaction(6140).
retractable_reaction(6151).
retractable_reaction(6152).
retractable_reaction(6160).
retractable_reaction(6181).
retractable_reaction(6182).
retractable_reaction(6191).
retractable_reaction(6192).
retractable_reaction(6211).
retractable_reaction(6212).
retractable_reaction(6241).
retractable_reaction(6242).
retractable_reaction(6250).
retractable_reaction(6260).
retractable_reaction(6270).
retractable_reaction(6290).
retractable_reaction(6300).
retractable_reaction(6310).
retractable_reaction(6320).
retractable_reaction(6330).
retractable_reaction(6340).
retractable_reaction(6360).
retractable_reaction(6370).
retractable_reaction(6390).
retractable_reaction(6400).
retractable_reaction(6410).
retractable_reaction(6430).
retractable_reaction(6440).
retractable_reaction(6450).
retractable_reaction(6461).
retractable_reaction(6462).
retractable_reaction(6470).
retractable_reaction(6480).
retractable_reaction(6490).
retractable_reaction(6500).
retractable_reaction(6510).
retractable_reaction(6520).
retractable_reaction(6531).
retractable_reaction(6532).
retractable_reaction(6541).
retractable_reaction(6542).
retractable_reaction(6550).
retractable_reaction(6560).
retractable_reaction(6570).
retractable_reaction(6580).
retractable_reaction(6610).
retractable_reaction(6620).
retractable_reaction(6640).
retractable_reaction(6650).
retractable_reaction(6680).
retractable_reaction(6710).
retractable_reaction(6730).
retractable_reaction(6740).
retractable_reaction(6760).
retractable_reaction(6780).
retractable_reaction(6790).
retractable_reaction(6801).
retractable_reaction(6802).
retractable_reaction(6810).
retractable_reaction(6820).
retractable_reaction(6830).
retractable_reaction(6840).
retractable_reaction(6850).
retractable_reaction(6860).
retractable_reaction(6870).
retractable_reaction(6900).
retractable_reaction(6931).
retractable_reaction(6932).
retractable_reaction(6941).
retractable_reaction(6942).
retractable_reaction(6950).
retractable_reaction(6960).
retractable_reaction(6970).
retractable_reaction(6980).
retractable_reaction(6990).
retractable_reaction(7000).
retractable_reaction(7021).
retractable_reaction(7022).
retractable_reaction(7031).
retractable_reaction(7032).
retractable_reaction(7060).
retractable_reaction(7080).
retractable_reaction(7090).
retractable_reaction(7110).
retractable_reaction(7120).
retractable_reaction(7130).
retractable_reaction(7151).
retractable_reaction(7152).
retractable_reaction(7161).
retractable_reaction(7162).
retractable_reaction(7170).
retractable_reaction(7190).
retractable_reaction(7220).
retractable_reaction(7230).
retractable_reaction(7240).
retractable_reaction(7250).
retractable_reaction(7260).
retractable_reaction(7290).
retractable_reaction(7301).
retractable_reaction(7302).
retractable_reaction(7320).
retractable_reaction(7350).
retractable_reaction(7370).
retractable_reaction(7380).
retractable_reaction(7390).
retractable_reaction(7400).
retractable_reaction(7411).
retractable_reaction(7412).
retractable_reaction(7420).
retractable_reaction(7430).
retractable_reaction(7440).
retractable_reaction(7460).
retractable_reaction(7480).
retractable_reaction(7511).
retractable_reaction(7512).
retractable_reaction(7520).
retractable_reaction(7530).
retractable_reaction(7550).
retractable_reaction(7561).
retractable_reaction(7562).
retractable_reaction(7590).
retractable_reaction(7600).
retractable_reaction(7610).
retractable_reaction(7620).
retractable_reaction(7630).
retractable_reaction(7641).
retractable_reaction(7642).
retractable_reaction(7650).
retractable_reaction(7660).
retractable_reaction(7671).
retractable_reaction(7672).
retractable_reaction(7681).
retractable_reaction(7682).
retractable_reaction(7691).
retractable_reaction(7692).
retractable_reaction(7701).
retractable_reaction(7702).
retractable_reaction(7710).
retractable_reaction(7720).
retractable_reaction(7730).
retractable_reaction(7741).
retractable_reaction(7742).
retractable_reaction(7751).
retractable_reaction(7752).
retractable_reaction(7761).
retractable_reaction(7762).
retractable_reaction(7770).
retractable_reaction(7780).
retractable_reaction(7790).
retractable_reaction(7800).
retractable_reaction(7820).
retractable_reaction(7841).
retractable_reaction(7842).
retractable_reaction(7861).
retractable_reaction(7862).
retractable_reaction(7870).
retractable_reaction(7880).
retractable_reaction(7891).
retractable_reaction(7892).
retractable_reaction(7901).
retractable_reaction(7902).
retractable_reaction(7921).
retractable_reaction(7922).
retractable_reaction(7931).
retractable_reaction(7932).
retractable_reaction(7940).
retractable_reaction(7950).
retractable_reaction(7961).
retractable_reaction(7962).
retractable_reaction(7980).
retractable_reaction(7990).
retractable_reaction(8000).
retractable_reaction(8010).
retractable_reaction(8020).
retractable_reaction(8041).
retractable_reaction(8042).
retractable_reaction(8061).
retractable_reaction(8062).
retractable_reaction(8070).
retractable_reaction(8080).
retractable_reaction(8091).
retractable_reaction(8092).
retractable_reaction(8111).
retractable_reaction(8112).
retractable_reaction(8120).
retractable_reaction(8130).
retractable_reaction(8150).
retractable_reaction(8160).
retractable_reaction(8181).
retractable_reaction(8182).
retractable_reaction(8190).
retractable_reaction(8200).
retractable_reaction(8210).
retractable_reaction(8231).
retractable_reaction(8232).
retractable_reaction(8241).
retractable_reaction(8242).
retractable_reaction(8251).
retractable_reaction(8252).
retractable_reaction(8261).
retractable_reaction(8262).
retractable_reaction(8271).
retractable_reaction(8272).
retractable_reaction(8281).
retractable_reaction(8282).
retractable_reaction(8300).
retractable_reaction(8320).
retractable_reaction(8341).
retractable_reaction(8342).
retractable_reaction(8351).
retractable_reaction(8352).
retractable_reaction(8360).
retractable_reaction(8370).
retractable_reaction(8390).
retractable_reaction(8400).
retractable_reaction(8411).
retractable_reaction(8412).
retractable_reaction(8421).
retractable_reaction(8422).
retractable_reaction(8431).
retractable_reaction(8432).
retractable_reaction(8441).
retractable_reaction(8442).
retractable_reaction(8451).
retractable_reaction(8452).
retractable_reaction(8461).
retractable_reaction(8462).
retractable_reaction(8481).
retractable_reaction(8482).
retractable_reaction(8491).
retractable_reaction(8492).
retractable_reaction(8511).
retractable_reaction(8512).
retractable_reaction(8521).
retractable_reaction(8522).
retractable_reaction(8531).
retractable_reaction(8532).
retractable_reaction(8551).
retractable_reaction(8552).
retractable_reaction(8561).
retractable_reaction(8562).
retractable_reaction(8571).
retractable_reaction(8572).
retractable_reaction(8581).
retractable_reaction(8582).
retractable_reaction(8591).
retractable_reaction(8592).
retractable_reaction(8601).
retractable_reaction(8602).
retractable_reaction(8611).
retractable_reaction(8612).
retractable_reaction(8621).
retractable_reaction(8622).
retractable_reaction(8631).
retractable_reaction(8632).
retractable_reaction(8641).
retractable_reaction(8642).
retractable_reaction(8651).
retractable_reaction(8652).
retractable_reaction(8661).
retractable_reaction(8662).
retractable_reaction(8671).
retractable_reaction(8672).
retractable_reaction(8711).
retractable_reaction(8712).
retractable_reaction(8741).
retractable_reaction(8742).
retractable_reaction(8751).
retractable_reaction(8752).
retractable_reaction(8781).
retractable_reaction(8782).
retractable_reaction(8791).
retractable_reaction(8792).
retractable_reaction(8801).
retractable_reaction(8802).
retractable_reaction(8811).
retractable_reaction(8812).
retractable_reaction(8821).
retractable_reaction(8822).
retractable_reaction(8831).
retractable_reaction(8832).
retractable_reaction(8841).
retractable_reaction(8842).
retractable_reaction(8851).
retractable_reaction(8852).
retractable_reaction(8861).
retractable_reaction(8862).
retractable_reaction(8871).
retractable_reaction(8872).
retractable_reaction(8881).
retractable_reaction(8882).
retractable_reaction(8891).
retractable_reaction(8892).
retractable_reaction(8901).
retractable_reaction(8902).
retractable_reaction(8931).
retractable_reaction(8932).
retractable_reaction(8941).
retractable_reaction(8942).
retractable_reaction(8951).
retractable_reaction(8952).
retractable_reaction(8971).
retractable_reaction(8972).
retractable_reaction(8991).
retractable_reaction(8992).
retractable_reaction(9021).
retractable_reaction(9022).
retractable_reaction(9041).
retractable_reaction(9042).
retractable_reaction(9051).
retractable_reaction(9052).
retractable_reaction(9061).
retractable_reaction(9062).
retractable_reaction(9071).
retractable_reaction(9072).
retractable_reaction(9081).
retractable_reaction(9082).
retractable_reaction(9131).
retractable_reaction(9132).
retractable_reaction(9141).
retractable_reaction(9142).
retractable_reaction(9161).
retractable_reaction(9162).
retractable_reaction(9181).
retractable_reaction(9182).
retractable_reaction(9191).
retractable_reaction(9192).
retractable_reaction(9201).
retractable_reaction(9202).
retractable_reaction(9211).
retractable_reaction(9212).
retractable_reaction(9221).
retractable_reaction(9222).
retractable_reaction(9231).
retractable_reaction(9232).
retractable_reaction(9241).
retractable_reaction(9242).
retractable_reaction(9261).
retractable_reaction(9262).
retractable_reaction(9271).
retractable_reaction(9272).
retractable_reaction(9291).
retractable_reaction(9292).
retractable_reaction(9301).
retractable_reaction(9302).
retractable_reaction(9321).
retractable_reaction(9322).
retractable_reaction(9331).
retractable_reaction(9332).
retractable_reaction(9361).
retractable_reaction(9362).
retractable_reaction(9371).
retractable_reaction(9372).
retractable_reaction(9401).
retractable_reaction(9402).
retractable_reaction(9411).
retractable_reaction(9412).
retractable_reaction(9421).
retractable_reaction(9422).
retractable_reaction(9431).
retractable_reaction(9432).
retractable_reaction(9441).
retractable_reaction(9442).
retractable_reaction(9461).
retractable_reaction(9462).
retractable_reaction(9471).
retractable_reaction(9472).
retractable_reaction(9481).
retractable_reaction(9482).
retractable_reaction(9491).
retractable_reaction(9492).
retractable_reaction(9501).
retractable_reaction(9502).
retractable_reaction(9521).
retractable_reaction(9522).
retractable_reaction(9531).
retractable_reaction(9532).
retractable_reaction(9561).
retractable_reaction(9562).
retractable_reaction(9581).
retractable_reaction(9582).
retractable_reaction(9591).
retractable_reaction(9592).
retractable_reaction(9611).
retractable_reaction(9612).
retractable_reaction(9621).
retractable_reaction(9622).
retractable_reaction(9631).
retractable_reaction(9632).
retractable_reaction(9641).
retractable_reaction(9642).
retractable_reaction(9651).
retractable_reaction(9652).
retractable_reaction(9661).
retractable_reaction(9662).
retractable_reaction(9671).
retractable_reaction(9672).
retractable_reaction(9681).
retractable_reaction(9682).
retractable_reaction(9691).
retractable_reaction(9692).
retractable_reaction(9711).
retractable_reaction(9712).
retractable_reaction(9731).
retractable_reaction(9732).
retractable_reaction(9751).
retractable_reaction(9752).
retractable_reaction(9771).
retractable_reaction(9772).
retractable_reaction(9791).
retractable_reaction(9792).
retractable_reaction(9801).
retractable_reaction(9802).
retractable_reaction(9811).
retractable_reaction(9812).
retractable_reaction(9821).
retractable_reaction(9822).
retractable_reaction(9841).
retractable_reaction(9842).
retractable_reaction(9851).
retractable_reaction(9852).
retractable_reaction(9861).
retractable_reaction(9862).
retractable_reaction(9871).
retractable_reaction(9872).
retractable_reaction(9881).
retractable_reaction(9882).
retractable_reaction(9891).
retractable_reaction(9892).
retractable_reaction(9901).
retractable_reaction(9902).
retractable_reaction(9921).
retractable_reaction(9922).
retractable_reaction(9931).
retractable_reaction(9932).
retractable_reaction(9941).
retractable_reaction(9942).
retractable_reaction(9951).
retractable_reaction(9952).
retractable_reaction(9961).
retractable_reaction(9962).
retractable_reaction(9981).
retractable_reaction(9982).
retractable_reaction(10011).
retractable_reaction(10012).
retractable_reaction(10021).
retractable_reaction(10022).
retractable_reaction(10031).
retractable_reaction(10032).
retractable_reaction(10051).
retractable_reaction(10052).
retractable_reaction(10061).
retractable_reaction(10062).
retractable_reaction(10071).
retractable_reaction(10072).
retractable_reaction(10081).
retractable_reaction(10082).
retractable_reaction(10091).
retractable_reaction(10092).
retractable_reaction(10131).
retractable_reaction(10132).
retractable_reaction(10151).
retractable_reaction(10152).
retractable_reaction(10161).
retractable_reaction(10162).
retractable_reaction(10181).
retractable_reaction(10182).
retractable_reaction(10201).
retractable_reaction(10202).
retractable_reaction(10221).
retractable_reaction(10222).
retractable_reaction(10241).
retractable_reaction(10242).
retractable_reaction(10251).
retractable_reaction(10252).
retractable_reaction(10261).
retractable_reaction(10262).
retractable_reaction(10281).
retractable_reaction(10282).
retractable_reaction(10291).
retractable_reaction(10292).
retractable_reaction(10301).
retractable_reaction(10302).
retractable_reaction(10321).
retractable_reaction(10322).
retractable_reaction(10331).
retractable_reaction(10332).
retractable_reaction(10351).
retractable_reaction(10352).
retractable_reaction(10371).
retractable_reaction(10372).
retractable_reaction(10391).
retractable_reaction(10392).
retractable_reaction(10401).
retractable_reaction(10402).
retractable_reaction(10411).
retractable_reaction(10412).
retractable_reaction(10421).
retractable_reaction(10422).
retractable_reaction(10441).
retractable_reaction(10442).
retractable_reaction(10451).
retractable_reaction(10452).
retractable_reaction(10461).
retractable_reaction(10462).
retractable_reaction(10481).
retractable_reaction(10482).
retractable_reaction(10491).
retractable_reaction(10492).
retractable_reaction(10501).
retractable_reaction(10502).
retractable_reaction(10521).
retractable_reaction(10522).
retractable_reaction(10541).
retractable_reaction(10542).
retractable_reaction(10561).
retractable_reaction(10562).
retractable_reaction(10581).
retractable_reaction(10582).
retractable_reaction(10591).
retractable_reaction(10592).
retractable_reaction(10601).
retractable_reaction(10602).
retractable_reaction(10611).
retractable_reaction(10612).
retractable_reaction(10621).
retractable_reaction(10622).
retractable_reaction(10641).
retractable_reaction(10642).
retractable_reaction(10651).
retractable_reaction(10652).
retractable_reaction(10661).
retractable_reaction(10662).
retractable_reaction(10681).
retractable_reaction(10682).
retractable_reaction(10691).
retractable_reaction(10692).
retractable_reaction(10701).
retractable_reaction(10702).
retractable_reaction(10711).
retractable_reaction(10712).
retractable_reaction(10721).
retractable_reaction(10722).
retractable_reaction(10741).
retractable_reaction(10742).
retractable_reaction(10761).
retractable_reaction(10762).
retractable_reaction(10781).
retractable_reaction(10782).
retractable_reaction(10791).
retractable_reaction(10792).
retractable_reaction(10811).
retractable_reaction(10812).
retractable_reaction(10821).
retractable_reaction(10822).
retractable_reaction(10831).
retractable_reaction(10832).
retractable_reaction(10841).
retractable_reaction(10842).
retractable_reaction(10861).
retractable_reaction(10862).
retractable_reaction(10871).
retractable_reaction(10872).
retractable_reaction(10920).
retractable_reaction(30010).
retractable_reaction(30020).
retractable_reaction(30030).
retractable_reaction(30040).
retractable_reaction(30050).
retractable_reaction(30060).
retractable_reaction(30070).
retractable_reaction(30080).
retractable_reaction(30090).
retractable_reaction(30100).
retractable_reaction(30110).
retractable_reaction(30120).
retractable_reaction(30130).
retractable_reaction(30140).
retractable_reaction(30150).
retractable_reaction(30160).


reactionID(E) :- assertable_reaction(E).
reactionID(E) :- retractable_reaction(E).
reactionID(E) :- certain_reaction(E).

enzyme_info(Reaction) :- catalyst(Reaction,Complex), Complex!=unknown.
catalyst(Reaction,unknown) :- not enzyme_info(Reaction).

component("YNL280C",756).
component("YLR056W",643).
component("YKR009C",624).
component("YMR083W",709).
component("YPL231W",857).
component("U46_",130).
component("YBR149W",218).
component("YBR149W",219).
component("YJR159W",592).
component("YGL001C",415).
component("YHR063C",498).
component("YML056C",693).
component("YLR432W",684).
component("YHR216W",518).
component("YAR075W",176).
component("YAR073W",175).
component("YCL030C",241).
component("YDR127W",314).
component("YJR139C",588).
component("YML075C",696).
component("YLR450W",687).
component("YKL085W",599).
component("YOR136W",806).
component("YNL009W",733).
component("YLR174W",657).
component("YDL066W",266).
component("YHR183W",512).
component("YGR256W",475).
component("YNL241C",749).
component("YOL059W",784).
component("YDL022W",259).
component("YCL018W",239).
component("YLR355C",678).
component("YIL074C",524).
component("YER081W",385).
component("YML054C",692).
component("YIL155C",531).
component("YPR191W",892).
component("YOR065W",798).
component("YJL166W",561).
component("YHR001W-A",484).
component("YGR183C",460).
component("YFR033C",411).
component("YEL024W",361).
component("YDR529C",353).
component("YBL045C",181).
component("Q0105",19).
component("YKR066C",629).
component("YKL026C",595).
component("YIR037W",541).
component("YBR244W",228).
component("YJR078W",580).
component("U58_",140).
component("U107_",28).
component("YGR255C",474).
component("U108_",29).
component("YBL098W",186).
component("YMR015C",706).
component("YHR007C",485).
component("YDR402C",341).
component("YGL055W",424).
component("YJR104C",582).
component("YHR008C",486).
component("YJL026W",543).
component("YIL066C",523).
component("YGR180C",459).
component("YER070W",383).
component("U37_",122).
component("U36_",121).
component("U35_",120).
component("YDR158W",322).
component("YJR009C",570).
component("YJL052W",544).
component("YGR192C",462).
component("YBR006W",191).
component("YPL276W",868).
component("YPL275W",867).
component("YOR388C",835).
component("YOR374W",832).
component("YER073W",384).
component("U68_",146).
component("YGL154C",431).
component("YBR115C",213).
component("U55_",137).
component("YER069W",382).
component("YOR323C",825).
component("U2_",115).
component("YER178W",396).
component("YBR221C",226).
component("YIL125W",528).
component("YBR166C",222).
component("YNL280C",757).
component("YGL012W",418).
component("YKL182W",611).
component("U57_",139).
component("YKL216W",621).
component("YDR044W",303).
component("YER014W",370).
component("YKR009C",625).
component("YIL160C",533).
component("YGL205W",436).
component("YKL141W",605).
component("YJR051W",575).
component("YEL047C",364).
component("YDL171C",288).
component("YOR375C",833).
component("YDL215C",292).
component("YAL062W",174).
component("U99_",171).
component("U100_",22).
component("YBR035C",201).
component("YMR189W",719).
component("U56_",138).
component("YKR080W",631).
component("YPL023C",839).
component("YGL125W",428).
component("YOR236W",818).
component("YGR204W",466).
component("YBR084W",207).
component("YLR142W",651).
component("U65_",144).
component("U62_",142).
component("YHR068W",499).
component("YKL150W",607).
component("YIL043C",521).
component("YHR042W",493).
component("YOR221C",816).
component("YMR145C",715).
component("YML120C",699).
component("YKL192C",615).
component("YKL055C",597).
component("YER061C",378).
component("YDL085W",269).
component("YBR046C",203).
component("YMR145C",716).
component("YML120C",700).
component("YKL192C",616).
component("YDL085W",270).
component("YFR030W",410).
component("YPL017C",838).
component("YFL018C",401).
component("YPL091W",842).
component("YDR353W",336).
component("YER042W",371).
component("YPR167C",887).
component("YJR137C",587).
component("YNL052W",736).
component("YMR256C",727).
component("YLR395C",682).
component("YLR038C",641).
component("YIL111W",527).
component("YHR051W",497).
component("YGL191W",434).
component("YGL187C",433).
component("YDL067C",267).
component("Q0275",21).
component("Q0250",20).
component("Q0045",18).
component("YPL266W",864).
component("YBR034C",200).
component("YPL273W",866).
component("YLL062C",637).
component("YDR410C",344).
component("YKR069W",630).
component("YOL096C",787).
component("U47_",131).
component("YER091C",389).
component("YJR073C",578).
component("YML008C",688).
component("YDL033C",261).
component("YOL096C",788).
component("YLR172C",656).
component("YBR263W",232).
component("YDR019C",299).
component("YDR408C",343).
component("YMR120C",714).
component("YLR028C",639).
component("YBL013W",177).
component("YJL130C",553).
component("YJL088W",547).
component("YPR074C",880).
component("YBR117C",214).
component("YLR354C",677).
component("YGR043C",446).
component("YMR108W",712).
component("YCL009C",238).
component("YMR062C",708).
component("YNL071W",737).
component("YIL160C",534).
component("YNR019W",766).
component("YCR048W",254).
component("U48_",132).
component("YNL277W",755).
component("YDR232W",325).
component("YFL017C",400).
component("YPL231W",858).
component("YER061C",379).
component("U86_",163).
component("YPL001W",837).
component("YDL052C",264).
component("U8_",166).
component("YDR148C",320).
component("YOR377W",834).
component("YGR177C",458).
component("YPL231W",859).
component("YLR195C",659).
component("YLR299W",669).
component("YGL017W",419).
component("YPR001W",870).
component("YNR001C",762).
component("YCR005C",249).
component("YML126C",702).
component("YDL182W",289).
component("YDL131W",279).
component("YNL117W",741).
component("YIR031C",539).
component("YPR160W",886).
component("YOR321W",824).
component("YJR143C",589).
component("YGR199W",464).
component("YDL095W",274).
component("YDL093W",273).
component("YAL023C",173).
component("YLR258W",666).
component("YFR015C",407).
component("YPL227C",855).
component("YOR103C",802).
component("YOR085W",800).
component("YMR149W",717).
component("YML019W",690).
component("YJL002C",542).
component("YEL002C",358).
component("YDL232W",293).
component("YCL043C",245).
component("YNL029C",734).
component("YIL085C",526).
component("YMR261C",728).
component("YML100W",698).
component("YBR126C",217).
component("YNL192W",748).
component("YBR038W",202).
component("YBR023C",198).
component("YEL011W",359).
component("YLR209C",660).
component("U104_",26).
component("U103_",25).
component("YOR209C",814).
component("YMR300C",730).
component("YDR354W",337).
component("YFR047C",412).
component("YJR133W",586).
component("U22_",109).
component("YLR209C",661).
component("YDR399W",339).
component("YPR176C",889).
component("YPL172C",849).
component("YNR041C",770).
component("YMR101C",710).
component("YDL090C",272).
component("YBR003W",190).
component("YBR002C",189).
component("YJL167W",562).
component("YJL167W",563).
component("YNL256W",751).
component("YPR069C",878).
component("YDR127W",315).
component("YHR190W",513).
component("YHR068W",500).
component("YLR303W",670).
component("YGR012W",443).
component("YML082W",697).
component("YJR130C",585).
component("YDR035W",301).
component("YBR249C",229).
component("YLR180W",658).
component("YDR502C",350).
component("YOR274W",821).
component("YOL143C",793).
component("YBR256C",231).
component("YHR137W",506).
component("YGL202W",435).
component("YLR027C",638).
component("YKL106W",601).
component("YOL140W",792).
component("YLR438W",686).
component("YKL104C",600).
component("YGR019W",444).
component("YDR111C",312).
component("U64_",143).
component("U51_",135).
component("YJR148W",590).
component("YHR208W",516).
component("YOR184W",811).
component("YNR058W",773).
component("YGL253W",441).
component("YFR053C",413).
component("YMR013C",705).
component("YMR205C",721).
component("YGR240C",470).
component("YLR240W",664).
component("YKL203C",618).
component("YJR066W",577).
component("YCR036W",253).
component("YGR194C",463).
component("YCL040W",244).
component("YJR105W",583).
component("U16_",72).
component("YPL188W",851).
component("YJR049C",574).
component("YEL041W",362).
component("U96_",170).
component("YKL001C",593).
component("YDR236C",326).
component("YML070W",695).
component("YFL053W",404).
component("YHL032C",482).
component("YLR133W",648).
component("YDR531W",355).
component("U83_",160).
component("U82_",159).
component("U81_",158).
component("YMR208W",722).
component("YPL203W",852).
component("YOR061W",797).
component("YKL166C",609).
component("YJL164C",560).
component("YIL035C",520).
component("YHR205W",515).
component("YHR102W",504).
component("YGL019W",420).
component("YHR025W",492).
component("YNR012W",764).
component("YPR121W",883).
component("YPL258C",861).
component("YOL055C",780).
component("YPL214C",854).
component("U1_",92).
component("YDR009W",298).
component("YBR020W",197).
component("YFR019W",408).
component("YDR208W",323).
component("YDR127W",316).
component("U21_",102).
component("U20_",97).
component("YDR147W",319).
component("YDR300C",333).
component("YCR012W",250).
component("YER052C",373).
component("U19_",91).
component("U18_",84).
component("U17_",78).
component("U76_",154).
component("YMR220W",724).
component("YER170W",395).
component("YDR226W",324).
component("YKL067W",598).
component("YOL055C",781).
component("YDR454C",347).
component("YOL061W",785).
component("YKL181W",610).
component("YHL011C",480).
component("YER099C",391).
component("YBL068W",184).
component("YOR143C",807).
component("YNL256W",752).
component("YLR328W",674).
component("YBR018C",193).
component("YBR018C",194).
component("YDL055C",265).
component("YGR007W",442).
component("YGR202C",465).
component("YLR328W",675).
component("YKR002W",623).
component("YDL045C",262).
component("YDL103C",277).
component("U94_",169).
component("YJR010W",571).
component("YBR029C",199).
component("YGL130W",429).
component("YDR530C",354).
component("YCL050C",246).
component("YPR190C",891).
component("YPR187W",890).
component("YPR110C",882).
component("YPR010C",872).
component("YOR341W",829).
component("YOR340C",828).
component("YOR224C",817).
component("YOR210W",815).
component("YOR207C",813).
component("YOR151C",808).
component("YOR116C",803).
component("YOL005C",774).
component("YNR003C",763).
component("YNL248C",750).
component("YNL151C",746).
component("YNL113W",740).
component("YKL144C",606).
component("YJR063W",576).
component("YJL148W",557).
component("YJL140W",556).
component("YIL021W",519).
component("YHR143W-A",507).
component("YGL070C",427).
component("YFL036W",403).
component("YDR404C",342).
component("YDR156W",321).
component("YDR045C",304).
component("YDL150W",286).
component("YDL140C",281).
component("YBR154C",221).
component("YPR175W",888).
component("YPL167C",848).
component("YOR330C",826).
component("YOL115W",791).
component("YNL299W",759).
component("YNL262W",753).
component("YNL102W",739).
component("YJR043C",573).
component("YJR006W",569).
component("YJL090C",548).
component("YIL139C",529).
component("YEL055C",365).
component("YDR419W",345).
component("YDR121W",313).
component("YDL102W",276).
component("YCR014C",251).
component("YBR278W",233).
component("YBL035C",179).
component("YKL035W",596).
component("YHL012W",481).
component("YHR123W",505).
component("YBR243C",227).
component("YNL130C",742).
component("YPL148C",846).
component("YOR251C",820).
component("YGR286C",477).
component("YDR058C",308).
component("YNR034W",769).
component("YHR163W",510).
component("YGR248W",472).
component("YCR073W-A",256).
component("YDL086W",271).
component("YOL011W",776).
component("YMR008C",704).
component("YMR006C",703).
component("U105_",27).
component("U101_",23).
component("YJL068C",545).
component("YPL072W",841).
component("YOR124C",804).
component("YNL186W",747).
component("YMR304W",731).
component("YMR223W",725).
component("YKR098C",634).
component("YJL197W",564).
component("YIL156W",532).
component("YFR010W",406).
component("YER151C",394).
component("YER144C",393).
component("YER098W",390).
component("YDR069C",309).
component("YDL122W",278).
component("YBR058C",204).
component("YBL067C",183).
component("YJR019C",572).
component("YDR272W",329).
component("U84_",161).
component("YDR481C",348).
component("YLR377C",680).
component("YDR074W",310).
component("YFR025C",409).
component("YPL179W",850).
component("YNR032W",767).
component("YML057W",694).
component("YML016C",689).
component("YLR433C",685).
component("YGR123C",452).
component("YER133W",392).
component("YER089C",387).
component("YDR436W",346).
component("YDR075W",311).
component("YDL188C",290).
component("YDL134C",280).
component("YDL047W",263).
component("YDL006W",257).
component("YBR125C",216).
component("YBL056W",182).
component("YPR073C",879).
component("YHR215W",517).
component("YDL024C",260).
component("YBR093C",211).
component("YBR092C",210).
component("YIL053W",522).
component("YER062C",380).
component("YHR046C",496).
component("U9_",172).
component("YGR208W",469).
component("YPL228W",856).
component("YMR180C",718).
component("YDL236W",294).
component("YJL155C",559).
component("U34_",119).
component("U33_",118).
component("U32_",117).
component("U30_",116).
component("U29_",114).
component("U28_",113).
component("U27_",112).
component("U26_",111).
component("U24_",110).
component("YHR044C",495).
component("YHR043C",494).
component("YOL064C",786).
component("YPL268W",865).
component("YOR360C",831).
component("YGL248W",440).
component("YKR031C",626).
component("YGL027C",422).
component("YLR286C",668).
component("YJR153W",591).
component("YJL221C",568).
component("YJL216C",566).
component("YIL172C",538).
component("YGR292W",479).
component("YGR287C",478).
component("YBR299W",237).
component("YBR184W",223).
component("YIL162W",535).
component("YPR026W",873).
component("YDR001C",296).
component("YBR001C",188).
component("YDR400W",340).
component("U102_",24).
component("YER043C",372).
component("YNL045W",735).
component("YLR160C",655).
component("YLR158C",654).
component("YLR157C",653).
component("YLR155C",652).
component("YDR321W",334).
component("YGL037C",423).
component("U43_",128).
component("U42_",127).
component("YDR242W",327).
component("YLR308W",673).
component("YLR307W",672).
component("U53_",136).
component("YLR420W",683).
component("YPL111W",844).
component("YIR032C",540).
component("YLR028C",640).
component("YHR144C",508).
component("YHR144C",509).
component("YCL030C",242).
component("YNL141W",743).
component("YBR153W",220).
component("YDL238C",295).
component("YNL141W",744).
component("YLR245C",665).
component("YML035C",691).
component("YGR204W",467).
component("YBR084W",208).
component("YJL126W",551).
component("U44_",129).
component("YDL100C",275).
component("U40_",125).
component("U39_",123).
component("YBR011C",192).
component("YHR201C",514).
component("YBR111C",212).
component("YBR252W",230).
component("YCL030C",243).
component("YER005W",369).
component("YBL099W",187).
component("YLR231C",662).
component("U88_",164).
component("YDR538W",357).
component("YLR134W",649).
component("YLR044C",642).
component("YGR087C",449).
component("YDR380W",338).
component("YDL080C",268).
component("YMR250W",726).
component("YKL184W",614).
component("YEL021W",360).
component("YNR043W",771).
component("U93_",168).
component("YDR047W",306).
component("YKL211C",619).
component("YKR097W",633).
component("YOL052C",779).
component("YGR170W",456).
component("YDR294C",330).
component("YEL046C",363).
component("YNR033W",768).
component("YPR006C",871).
component("YER065C",381).
component("YKL211C",620).
component("YER090W",388).
component("YDR127W",317).
component("YPL281C",869).
component("YOR393W",836).
component("YMR323W",732).
component("YHR174W",511).
component("YGR254W",473).
component("YPL262W",862).
component("YGL026C",421).
component("YGR155W",455).
component("YLR304C",671).
component("YJL200C",565).
component("YGL009C",417).
component("YNL316C",760).
component("YKL182W",612).
component("YPL212C",853).
component("YNL292W",758).
component("YGL063W",426).
component("YFL001W",398).
component("YOR278W",822).
component("YCR053W",255).
component("YDR127W",318).
component("YGL148W",430).
component("YIL168W",537).
component("YIL167W",536).
component("YCL064C",247).
component("YCL064C",248).
component("YHR018C",488).
component("YLR359W",679).
component("YFR055W",414).
component("YJL121C",550).
component("YBR019C",195).
component("YBR019C",196).
component("YDR050C",307).
component("YDR007W",297).
component("YOR095C",801).
component("YER003C",368).
component("YBR196C",224).
component("YGL001C",416).
component("YPL117C",845).
component("U14_",59).
component("YOL056W",782).
component("YKL152C",608).
component("YDL021W",258).
component("YMR105C",711).
component("YKL127W",603).
component("YEL058W",366).
component("YPR060C",877).
component("YHR072W",501).
component("YJL153C",558).
component("YGR264C",476).
component("YGR171C",457).
component("YHR011W",487).
component("YDR023W",300).
component("YPL104W",843).
component("YLL018C",635).
component("YPR081C",881).
component("YBR121C",215).
component("YHR020W",491).
component("YER087W",386).
component("YOL033W",778).
component("YGL245W",439).
component("YOR168W",809).
component("YHR091C",503).
component("YDR341C",335).
component("YOL097C",789).
component("YDR268W",328).
component("YPR047W",876).
component("YLR060W",644).
component("YFL022C",402).
component("YPR033C",874).
component("YHR019C",489).
component("YHR019C",490).
component("YKL194C",617).
component("YIL078W",525).
component("YPL160W",847).
component("YLR382C",681).
component("YPL040C",840).
component("YBL076C",185).
component("YNL073W",738).
component("YDR037W",302).
component("YOR335C",827).
component("YGR094W",450).
component("YGR244C",471).
component("YPR035W",875).
component("YIL145C",530).
component("U89_",165).
component("YOR241W",819).
component("YMR113W",713).
component("YKL132C",604).
component("YJL101C",549).
component("YGL234W",437).
component("YER183C",397).
component("U90_",167).
component("YNR057C",772).
component("YDL141W",282).
component("YDL141W",283).
component("YGL234W",438).
component("YDL141W",284).
component("YGR204W",468).
component("YOL058W",783).
component("YDL141W",285).
component("YHR074W",502).
component("YMR217W",723).
component("YPR145W",885).
component("YGR124W",453).
component("YOR303W",823).
component("YJR109C",584).
component("YJL130C",554).
component("YGL062W",425).
component("YBR218C",225).
component("YPL231W",860).
component("YNR016C",765).
component("YKL182W",613).
component("YGR037C",445).
component("YOR005C",795).
component("YDL164C",287).
component("YJL087C",546).
component("YOL010W",775).
component("YPR138C",884).
component("YPL265W",863).
component("YOR348C",830).
component("YOR192C",812).
component("YOR171C",810).
component("YOR130C",805).
component("YOR071C",799).
component("YOR011W",796).
component("YOL156W",794).
component("YOL103W",790).
component("YOL020W",777).
component("YNL318C",761).
component("YNL270C",754).
component("YNL142W",745).
component("YMR272C",729).
component("YMR202W",720).
component("YMR056C",707).
component("YML123C",701).
component("YLR348C",676).
component("YLR260W",667).
component("YLR237W",663).
component("YLR138W",650).
component("YLR100C",647).
component("YLR092W",646).
component("YLR081W",645).
component("YLL061W",636).
component("YKR093W",632).
component("YKR053C",628).
component("YKR039W",627).
component("YKL217W",622).
component("YKL120W",602).
component("YKL004W",594).
component("YJR095W",581).
component("YJR077C",579).
component("YJL219W",567).
component("YJL134W",555).
component("YJL129C",552).
component("YHL036W",483).
component("YGR191W",461).
component("YGR125W",454).
component("YGR121C",451).
component("YGR065C",448).
component("YGR055W",447).
component("YGL186C",432).
component("YFL055W",405).
component("YFL011W",399).
component("YER060W-A",377).
component("YER060W",376).
component("YER056C",375).
component("YER053C",374).
component("YEL063C",367).
component("YDR536W",356).
component("YDR508C",352).
component("YDR503C",351).
component("YDR497C",349).
component("YDR297W",332).
component("YDR294C",331).
component("YDR046C",305).
component("YDL210W",291).
component("YCR028C",252).
component("YCL025C",240).
component("YBR298C",236).
component("YBR294W",235).
component("YBR291C",234).
component("YBR085W",209).
component("YBR069C",206).
component("YBR068C",205).
component("YBL042C",180).
component("YBL030C",178).
component("U85_",162).
component("U7_",157).
component("U79_",156).
component("U78_",155).
component("U75_",153).
component("U74_",152).
component("U73_",151).
component("U72_",150).
component("U70_",149).
component("U6_",148).
component("U69_",147).
component("U66_",145).
component("U5_",141).
component("U50_",134).
component("U4_",133).
component("U41_",126).
component("U3_",124).
component("U229_",108).
component("U228_",107).
component("U227_",106).
component("U223_",105).
component("U222_",104).
component("U220_",103).
component("U219_",101).
component("U218_",100).
component("U214_",99).
component("U213_",98).
component("U207_",96).
component("U205_",95).
component("U201_",94).
component("U200_",93).
component("U197_",90).
component("U195_",89).
component("U193_",88).
component("U192_",87).
component("U191_",86).
component("U190_",85).
component("U187_",83).
component("U186_",82).
component("U185_",81).
component("U184_",80).
component("U181_",79).
component("U179_",77).
component("U176_",76).
component("U175_",75).
component("U174_",74).
component("U171_",73).
component("U167_",71).
component("U166_",70).
component("U165_",69).
component("U164_",68).
component("U163_",67).
component("U162_",66).
component("U161_",65).
component("U155_",64).
component("U154_",63).
component("U153_",62).
component("U152_",61).
component("U150_",60).
component("U147_",58).
component("U146_",57).
component("U145_",56).
component("U144_",55).
component("U143_",54).
component("U142_",53).
component("U141_",52).
component("U13_",51).
component("U139_",50).
component("U138_",49).
component("U136_",48).
component("U134_",47).
component("U130_",46).
component("U12_",45).
component("U128_",44).
component("U125_",43).
component("U122_",42).
component("U121_",41).
component("U120_",40).
component("U119_",39).
component("U117_",38).
component("U116_",37).
component("U115_",36).
component("U114_",35).
component("U112_",34).
component("U111_",33).
component("U110_",32).
component("U10_",31).
component("U109_",30).
component("I01179",17).
component("I00631",16).
component("I00493",15).
component("I00463",14).
component("I00279",13).
component("I00166",12).
component("I00119",11).
component("I00108",10).
component("I00074",9).
component("I00008",8).
component("I00007",7).
component("I00006",6).
component("I00005",5).
component("I00004",4).
component("I00003",3).
component("I00002",2).
component("I00001",1).


catalyst(6390,756).
catalyst(6300,643).
catalyst(7301,624).
catalyst(7302,624).
catalyst(7511,709).
catalyst(7512,709).
catalyst(10781,857).
catalyst(10782,857).
catalyst(10791,857).
catalyst(10792,857).
catalyst(10811,857).
catalyst(10812,857).
catalyst(10821,857).
catalyst(10822,857).
catalyst(10831,857).
catalyst(10832,857).
catalyst(10841,857).
catalyst(10842,857).
catalyst(4510,130).
catalyst(10391,218).
catalyst(10392,218).
catalyst(4850,219).
catalyst(7780,592).
catalyst(10241,415).
catalyst(10242,415).
catalyst(10251,415).
catalyst(10252,415).
catalyst(10261,415).
catalyst(10262,415).
catalyst(10281,415).
catalyst(10282,415).
catalyst(10291,415).
catalyst(10292,415).
catalyst(10301,415).
catalyst(10302,415).
catalyst(10321,415).
catalyst(10322,415).
catalyst(10331,415).
catalyst(10332,415).
catalyst(10351,415).
catalyst(10352,415).
catalyst(10371,415).
catalyst(10372,415).
catalyst(2350,498).
catalyst(6040,693).
catalyst(6040,684).
catalyst(6040,518).
catalyst(6040,176).
catalyst(6040,175).
catalyst(3800,241).
catalyst(3730,314).
catalyst(4600,588).
catalyst(6531,696).
catalyst(6532,696).
catalyst(6531,687).
catalyst(6532,687).
catalyst(8041,599).
catalyst(8042,599).
catalyst(10861,806).
catalyst(10862,806).
catalyst(8130,733).
catalyst(8150,733).
catalyst(8130,657).
catalyst(8150,657).
catalyst(8160,266).
catalyst(7940,512).
catalyst(7940,475).
catalyst(7961,749).
catalyst(7962,749).
catalyst(3020,784).
catalyst(3020,259).
catalyst(4170,239).
catalyst(2340,678).
catalyst(4710,524).
catalyst(4710,385).
catalyst(7370,692).
catalyst(3000,531).
catalyst(10651,892).
catalyst(10652,892).
catalyst(10651,798).
catalyst(10652,798).
catalyst(10651,561).
catalyst(10652,561).
catalyst(10651,484).
catalyst(10652,484).
catalyst(10651,460).
catalyst(10652,460).
catalyst(10651,411).
catalyst(10652,411).
catalyst(7400,361).
catalyst(10651,353).
catalyst(10652,353).
catalyst(10651,181).
catalyst(10652,181).
catalyst(10651,19).
catalyst(10652,19).
catalyst(10071,629).
catalyst(10072,629).
catalyst(3141,595).
catalyst(3142,595).
catalyst(3141,541).
catalyst(3142,541).
catalyst(3141,228).
catalyst(3142,228).
catalyst(3520,580).
catalyst(3420,140).
catalyst(1860,28).
catalyst(1820,474).
catalyst(1840,29).
catalyst(3490,186).
catalyst(6290,706).
catalyst(6400,485).
catalyst(10031,341).
catalyst(10032,341).
catalyst(10051,341).
catalyst(10052,341).
catalyst(10061,341).
catalyst(10062,341).
catalyst(10021,424).
catalyst(10022,424).
catalyst(10011,582).
catalyst(10012,582).
catalyst(10011,486).
catalyst(10012,486).
catalyst(10601,543).
catalyst(10602,543).
catalyst(10611,543).
catalyst(10612,543).
catalyst(10621,543).
catalyst(10622,543).
catalyst(10641,543).
catalyst(10642,543).
catalyst(5140,523).
catalyst(10601,459).
catalyst(10602,459).
catalyst(10611,459).
catalyst(10612,459).
catalyst(10621,459).
catalyst(10622,459).
catalyst(10641,459).
catalyst(10642,459).
catalyst(5110,383).
catalyst(5120,383).
catalyst(5140,383).
catalyst(5080,122).
catalyst(5090,121).
catalyst(5100,120).
catalyst(4620,322).
catalyst(8271,570).
catalyst(8272,570).
catalyst(8271,544).
catalyst(8272,544).
catalyst(8271,462).
catalyst(8272,462).
catalyst(5010,191).
catalyst(7350,868).
catalyst(7350,867).
catalyst(7350,835).
catalyst(3540,832).
catalyst(3550,832).
catalyst(3211,384).
catalyst(3212,384).
catalyst(3540,384).
catalyst(3220,146).
catalyst(10741,431).
catalyst(10742,431).
catalyst(10761,431).
catalyst(10762,431).
catalyst(4100,213).
catalyst(3450,137).
catalyst(4030,382).
catalyst(3290,825).
catalyst(3300,825).
catalyst(7440,115).
catalyst(8210,396).
catalyst(10681,226).
catalyst(10682,226).
catalyst(10691,226).
catalyst(10692,226).
catalyst(10701,226).
catalyst(10702,226).
catalyst(10711,226).
catalyst(10712,226).
catalyst(10721,226).
catalyst(10722,226).
catalyst(8120,528).
catalyst(3660,222).
catalyst(10221,757).
catalyst(10222,757).
catalyst(10201,418).
catalyst(10202,418).
catalyst(7021,611).
catalyst(7022,611).
catalyst(3430,139).
catalyst(5911,621).
catalyst(5912,621).
catalyst(1950,303).
catalyst(1940,370).
catalyst(6990,625).
catalyst(7000,625).
catalyst(6990,533).
catalyst(7000,533).
catalyst(6990,436).
catalyst(7000,436).
catalyst(7411,605).
catalyst(7412,605).
catalyst(8091,605).
catalyst(8092,605).
catalyst(8070,575).
catalyst(8080,364).
catalyst(10181,288).
catalyst(10182,288).
catalyst(4910,833).
catalyst(4920,292).
catalyst(4910,174).
catalyst(2210,171).
catalyst(2200,22).
catalyst(2711,201).
catalyst(2712,201).
catalyst(2721,201).
catalyst(2722,201).
catalyst(2731,201).
catalyst(2732,201).
catalyst(4551,719).
catalyst(4552,719).
catalyst(3440,138).
catalyst(2380,631).
catalyst(2450,839).
catalyst(2450,428).
catalyst(2490,818).
catalyst(2500,818).
catalyst(2431,466).
catalyst(2432,466).
catalyst(2441,207).
catalyst(2442,207).
catalyst(3230,651).
catalyst(3320,144).
catalyst(3350,142).
catalyst(3880,499).
catalyst(10161,607).
catalyst(10162,607).
catalyst(10161,521).
catalyst(10162,521).
catalyst(7420,493).
catalyst(7170,816).
catalyst(7190,816).
catalyst(7220,816).
catalyst(7230,816).
catalyst(7240,816).
catalyst(7250,816).
catalyst(7430,715).
catalyst(7260,699).
catalyst(7170,615).
catalyst(7190,615).
catalyst(7220,615).
catalyst(7230,615).
catalyst(7240,615).
catalyst(7250,615).
catalyst(7260,615).
catalyst(7170,597).
catalyst(7190,597).
catalyst(7220,597).
catalyst(7230,597).
catalyst(7240,597).
catalyst(7250,597).
catalyst(7170,378).
catalyst(7190,378).
catalyst(7220,378).
catalyst(7230,378).
catalyst(7240,378).
catalyst(7250,378).
catalyst(7430,269).
catalyst(10151,203).
catalyst(10152,203).
catalyst(10131,716).
catalyst(10132,716).
catalyst(10131,700).
catalyst(10132,700).
catalyst(10131,616).
catalyst(10132,616).
catalyst(10131,270).
catalyst(10132,270).
catalyst(4371,410).
catalyst(4372,410).
catalyst(10091,838).
catalyst(10092,838).
catalyst(10701,838).
catalyst(10702,838).
catalyst(10711,838).
catalyst(10712,838).
catalyst(10091,401).
catalyst(10092,401).
catalyst(10701,401).
catalyst(10702,401).
catalyst(10711,401).
catalyst(10712,401).
catalyst(3130,842).
catalyst(5750,336).
catalyst(10081,371).
catalyst(10082,371).
catalyst(4330,887).
catalyst(4371,587).
catalyst(4372,587).
catalyst(10661,736).
catalyst(10662,736).
catalyst(10661,727).
catalyst(10662,727).
catalyst(10661,682).
catalyst(10662,682).
catalyst(10661,641).
catalyst(10662,641).
catalyst(10661,527).
catalyst(10662,527).
catalyst(10661,497).
catalyst(10662,497).
catalyst(10661,434).
catalyst(10662,434).
catalyst(10661,433).
catalyst(10662,433).
catalyst(10661,267).
catalyst(10662,267).
catalyst(10661,21).
catalyst(10662,21).
catalyst(10661,20).
catalyst(10662,20).
catalyst(7390,18).
catalyst(1850,864).
catalyst(3770,200).
catalyst(4750,866).
catalyst(4750,637).
catalyst(9961,344).
catalyst(9962,344).
catalyst(1900,630).
catalyst(9951,787).
catalyst(9952,787).
catalyst(4470,131).
catalyst(4480,389).
catalyst(6860,578).
catalyst(6870,578).
catalyst(6320,688).
catalyst(9981,261).
catalyst(9982,261).
catalyst(1810,788).
catalyst(4400,656).
catalyst(4681,232).
catalyst(4682,232).
catalyst(4640,299).
catalyst(6140,343).
catalyst(6071,714).
catalyst(6072,714).
catalyst(6081,714).
catalyst(6082,714).
catalyst(6081,639).
catalyst(6082,639).
catalyst(2370,177).
catalyst(5930,553).
catalyst(3990,547).
catalyst(7901,880).
catalyst(7902,880).
catalyst(7901,214).
catalyst(7902,214).
catalyst(7891,677).
catalyst(7892,677).
catalyst(7891,446).
catalyst(7892,446).
catalyst(4250,712).
catalyst(4260,712).
catalyst(10561,238).
catalyst(10562,238).
catalyst(10581,238).
catalyst(10582,238).
catalyst(10591,238).
catalyst(10592,238).
catalyst(10721,238).
catalyst(10722,238).
catalyst(4050,708).
catalyst(10541,737).
catalyst(10542,737).
catalyst(10701,737).
catalyst(10702,737).
catalyst(10711,737).
catalyst(10712,737).
catalyst(7290,534).
catalyst(9941,766).
catalyst(9942,766).
catalyst(9941,254).
catalyst(9942,254).
catalyst(4360,132).
catalyst(4451,755).
catalyst(4452,755).
catalyst(2000,325).
catalyst(4991,400).
catalyst(4992,400).
catalyst(10451,858).
catalyst(10452,858).
catalyst(10461,858).
catalyst(10462,858).
catalyst(10481,858).
catalyst(10482,858).
catalyst(10491,858).
catalyst(10492,858).
catalyst(10501,858).
catalyst(10502,858).
catalyst(10521,858).
catalyst(10522,858).
catalyst(7130,379).
catalyst(2651,163).
catalyst(2652,163).
catalyst(9931,837).
catalyst(9932,837).
catalyst(6950,264).
catalyst(6950,166).
catalyst(10441,320).
catalyst(10442,320).
catalyst(9921,834).
catalyst(9922,834).
catalyst(9921,458).
catalyst(9922,458).
catalyst(9771,859).
catalyst(9772,859).
catalyst(9791,859).
catalyst(9792,859).
catalyst(9801,859).
catalyst(9802,859).
catalyst(9811,859).
catalyst(9812,859).
catalyst(9821,859).
catalyst(9822,859).
catalyst(9841,859).
catalyst(9842,859).
catalyst(9851,859).
catalyst(9852,859).
catalyst(9861,859).
catalyst(9862,859).
catalyst(9871,859).
catalyst(9872,859).
catalyst(9881,859).
catalyst(9882,859).
catalyst(9891,859).
catalyst(9892,859).
catalyst(9901,859).
catalyst(9902,859).
catalyst(3180,659).
catalyst(3120,669).
catalyst(9751,419).
catalyst(9752,419).
catalyst(8190,870).
catalyst(8190,762).
catalyst(8200,249).
catalyst(6541,702).
catalyst(6542,702).
catalyst(7520,289).
catalyst(7530,289).
catalyst(7530,279).
catalyst(8010,741).
catalyst(8010,539).
catalyst(7600,886).
catalyst(3070,824).
catalyst(3070,589).
catalyst(3070,464).
catalyst(3070,274).
catalyst(3070,273).
catalyst(3070,173).
catalyst(7590,666).
catalyst(7590,407).
catalyst(9731,855).
catalyst(9732,855).
catalyst(9711,802).
catalyst(9712,802).
catalyst(9711,800).
catalyst(9712,800).
catalyst(9711,717).
catalyst(9712,717).
catalyst(9711,690).
catalyst(9712,690).
catalyst(9711,542).
catalyst(9712,542).
catalyst(9711,358).
catalyst(9712,358).
catalyst(9711,293).
catalyst(9712,293).
catalyst(9711,245).
catalyst(9712,245).
catalyst(9691,734).
catalyst(9692,734).
catalyst(9691,526).
catalyst(9692,526).
catalyst(7630,728).
catalyst(7630,698).
catalyst(7630,217).
catalyst(4960,748).
catalyst(4960,202).
catalyst(4960,198).
catalyst(7600,359).
catalyst(2041,660).
catalyst(2042,660).
catalyst(2051,660).
catalyst(2052,660).
catalyst(5561,660).
catalyst(5562,660).
catalyst(5581,660).
catalyst(5582,660).
catalyst(5591,660).
catalyst(5592,660).
catalyst(5601,660).
catalyst(5602,660).
catalyst(5611,660).
catalyst(5612,660).
catalyst(5621,660).
catalyst(5622,660).
catalyst(2121,26).
catalyst(2122,26).
catalyst(2131,25).
catalyst(2132,25).
catalyst(2020,814).
catalyst(2220,814).
catalyst(6160,730).
catalyst(3620,337).
catalyst(2110,412).
catalyst(2190,412).
catalyst(5550,586).
catalyst(5301,109).
catalyst(5302,109).
catalyst(5801,661).
catalyst(5802,661).
catalyst(5310,339).
catalyst(1880,889).
catalyst(1880,849).
catalyst(1880,770).
catalyst(1880,710).
catalyst(1880,272).
catalyst(1880,190).
catalyst(1880,189).
catalyst(6450,562).
catalyst(6440,563).
catalyst(2520,751).
catalyst(2530,751).
catalyst(3930,878).
catalyst(3710,315).
catalyst(6430,513).
catalyst(9671,500).
catalyst(9672,500).
catalyst(4430,670).
catalyst(4350,443).
catalyst(4421,697).
catalyst(4422,697).
catalyst(9591,585).
catalyst(9592,585).
catalyst(9611,585).
catalyst(9612,585).
catalyst(9621,585).
catalyst(9622,585).
catalyst(9631,585).
catalyst(9632,585).
catalyst(9641,585).
catalyst(9642,585).
catalyst(9651,585).
catalyst(9652,585).
catalyst(9661,585).
catalyst(9662,585).
catalyst(3760,301).
catalyst(3760,229).
catalyst(4410,658).
catalyst(4410,350).
catalyst(9681,821).
catalyst(9682,821).
catalyst(10411,793).
catalyst(10412,793).
catalyst(10421,793).
catalyst(10422,793).
catalyst(2820,231).
catalyst(3650,506).
catalyst(3671,506).
catalyst(3672,506).
catalyst(3650,435).
catalyst(3571,638).
catalyst(3572,638).
catalyst(3571,601).
catalyst(3572,601).
catalyst(4020,792).
catalyst(3980,686).
catalyst(5000,600).
catalyst(5020,444).
catalyst(4781,312).
catalyst(4782,312).
catalyst(3330,143).
catalyst(4121,135).
catalyst(4122,135).
catalyst(4271,590).
catalyst(4272,590).
catalyst(4281,590).
catalyst(4282,590).
catalyst(4291,590).
catalyst(4292,590).
catalyst(4301,516).
catalyst(4302,516).
catalyst(4311,516).
catalyst(4312,516).
catalyst(2691,811).
catalyst(2692,811).
catalyst(4700,811).
catalyst(2641,773).
catalyst(2642,773).
catalyst(8360,441).
catalyst(8370,441).
catalyst(8390,441).
catalyst(8360,413).
catalyst(8370,413).
catalyst(8390,413).
catalyst(3090,705).
catalyst(8320,721).
catalyst(8300,470).
catalyst(8320,470).
catalyst(6760,664).
catalyst(6760,618).
catalyst(6760,577).
catalyst(7870,253).
catalyst(7880,253).
catalyst(4840,463).
catalyst(8370,244).
catalyst(8400,244).
catalyst(5520,583).
catalyst(5840,72).
catalyst(2070,851).
catalyst(2160,851).
catalyst(2070,574).
catalyst(2160,574).
catalyst(2070,362).
catalyst(2160,362).
catalyst(2270,170).
catalyst(4380,593).
catalyst(2790,326).
catalyst(2800,326).
catalyst(3030,695).
catalyst(3030,404).
catalyst(3010,482).
catalyst(6850,648).
catalyst(2320,355).
catalyst(2740,160).
catalyst(2750,159).
catalyst(2760,158).
catalyst(6490,722).
catalyst(6500,722).
catalyst(6510,722).
catalyst(6520,722).
catalyst(9561,852).
catalyst(9562,852).
catalyst(9561,797).
catalyst(9562,797).
catalyst(9561,609).
catalyst(9562,609).
catalyst(9561,560).
catalyst(9562,560).
catalyst(9561,520).
catalyst(9562,520).
catalyst(9561,515).
catalyst(9562,515).
catalyst(9561,504).
catalyst(9562,504).
catalyst(9561,420).
catalyst(9562,420).
catalyst(4590,492).
catalyst(5830,764).
catalyst(2950,883).
catalyst(2950,861).
catalyst(2950,780).
catalyst(2910,854).
catalyst(7790,92).
catalyst(9581,298).
catalyst(9582,298).
catalyst(7770,197).
catalyst(6740,408).
catalyst(6740,323).
catalyst(3720,316).
catalyst(5330,102).
catalyst(5340,97).
catalyst(6820,319).
catalyst(3310,333).
catalyst(8261,250).
catalyst(8262,250).
catalyst(4630,373).
catalyst(5361,91).
catalyst(5362,91).
catalyst(5701,84).
catalyst(5702,84).
catalyst(5711,78).
catalyst(5712,78).
catalyst(2891,154).
catalyst(2892,154).
catalyst(6480,724).
catalyst(5471,395).
catalyst(5472,395).
catalyst(5481,395).
catalyst(5482,395).
catalyst(5491,324).
catalyst(5492,324).
catalyst(5511,324).
catalyst(5512,324).
catalyst(5371,598).
catalyst(5372,598).
catalyst(5381,598).
catalyst(5382,598).
catalyst(5391,598).
catalyst(5392,598).
catalyst(5401,598).
catalyst(5402,598).
catalyst(5411,598).
catalyst(5412,598).
catalyst(5421,598).
catalyst(5422,598).
catalyst(5431,598).
catalyst(5432,598).
catalyst(5451,598).
catalyst(5452,598).
catalyst(2940,781).
catalyst(6181,347).
catalyst(6182,347).
catalyst(6191,347).
catalyst(6192,347).
catalyst(6241,785).
catalyst(6242,785).
catalyst(6241,610).
catalyst(6242,610).
catalyst(6241,480).
catalyst(6242,480).
catalyst(6241,391).
catalyst(6242,391).
catalyst(6241,184).
catalyst(6242,184).
catalyst(2970,807).
catalyst(2980,807).
catalyst(2560,752).
catalyst(9531,674).
catalyst(9532,674).
catalyst(7761,193).
catalyst(7762,193).
catalyst(7641,194).
catalyst(7642,194).
catalyst(7820,265).
catalyst(6810,442).
catalyst(6840,465).
catalyst(2090,675).
catalyst(2100,675).
catalyst(2180,675).
catalyst(9521,623).
catalyst(9522,623).
catalyst(2780,262).
catalyst(4971,277).
catalyst(4972,277).
catalyst(2280,169).
catalyst(2290,169).
catalyst(4390,571).
catalyst(6931,199).
catalyst(6932,199).
catalyst(6941,199).
catalyst(6942,199).
catalyst(9421,429).
catalyst(9422,429).
catalyst(5960,354).
catalyst(5940,246).
catalyst(9481,891).
catalyst(9482,891).
catalyst(9491,891).
catalyst(9492,891).
catalyst(9501,891).
catalyst(9502,891).
catalyst(9521,891).
catalyst(9522,891).
catalyst(9481,890).
catalyst(9482,890).
catalyst(9491,890).
catalyst(9492,890).
catalyst(9501,890).
catalyst(9502,890).
catalyst(9521,890).
catalyst(9522,890).
catalyst(9481,882).
catalyst(9482,882).
catalyst(9491,882).
catalyst(9492,882).
catalyst(9501,882).
catalyst(9502,882).
catalyst(9521,882).
catalyst(9522,882).
catalyst(9481,872).
catalyst(9482,872).
catalyst(9491,872).
catalyst(9492,872).
catalyst(9501,872).
catalyst(9502,872).
catalyst(9521,872).
catalyst(9522,872).
catalyst(9481,829).
catalyst(9482,829).
catalyst(9491,829).
catalyst(9492,829).
catalyst(9501,829).
catalyst(9502,829).
catalyst(9521,829).
catalyst(9522,829).
catalyst(9481,828).
catalyst(9482,828).
catalyst(9491,828).
catalyst(9492,828).
catalyst(9501,828).
catalyst(9502,828).
catalyst(9521,828).
catalyst(9522,828).
catalyst(9481,817).
catalyst(9482,817).
catalyst(9491,817).
catalyst(9492,817).
catalyst(9501,817).
catalyst(9502,817).
catalyst(9521,817).
catalyst(9522,817).
catalyst(9481,815).
catalyst(9482,815).
catalyst(9491,815).
catalyst(9492,815).
catalyst(9501,815).
catalyst(9502,815).
catalyst(9521,815).
catalyst(9522,815).
catalyst(9481,813).
catalyst(9482,813).
catalyst(9491,813).
catalyst(9492,813).
catalyst(9501,813).
catalyst(9502,813).
catalyst(9521,813).
catalyst(9522,813).
catalyst(9481,808).
catalyst(9482,808).
catalyst(9491,808).
catalyst(9492,808).
catalyst(9501,808).
catalyst(9502,808).
catalyst(9521,808).
catalyst(9522,808).
catalyst(9481,803).
catalyst(9482,803).
catalyst(9491,803).
catalyst(9492,803).
catalyst(9501,803).
catalyst(9502,803).
catalyst(9521,803).
catalyst(9522,803).
catalyst(9481,774).
catalyst(9482,774).
catalyst(9491,774).
catalyst(9492,774).
catalyst(9501,774).
catalyst(9502,774).
catalyst(9521,774).
catalyst(9522,774).
catalyst(9481,763).
catalyst(9482,763).
catalyst(9491,763).
catalyst(9492,763).
catalyst(9501,763).
catalyst(9502,763).
catalyst(9521,763).
catalyst(9522,763).
catalyst(9481,750).
catalyst(9482,750).
catalyst(9491,750).
catalyst(9492,750).
catalyst(9501,750).
catalyst(9502,750).
catalyst(9521,750).
catalyst(9522,750).
catalyst(9481,746).
catalyst(9482,746).
catalyst(9491,746).
catalyst(9492,746).
catalyst(9501,746).
catalyst(9502,746).
catalyst(9521,746).
catalyst(9522,746).
catalyst(9481,740).
catalyst(9482,740).
catalyst(9491,740).
catalyst(9492,740).
catalyst(9501,740).
catalyst(9502,740).
catalyst(9521,740).
catalyst(9522,740).
catalyst(9481,606).
catalyst(9482,606).
catalyst(9491,606).
catalyst(9492,606).
catalyst(9501,606).
catalyst(9502,606).
catalyst(9521,606).
catalyst(9522,606).
catalyst(9481,576).
catalyst(9482,576).
catalyst(9491,576).
catalyst(9492,576).
catalyst(9501,576).
catalyst(9502,576).
catalyst(9521,576).
catalyst(9522,576).
catalyst(9481,557).
catalyst(9482,557).
catalyst(9491,557).
catalyst(9492,557).
catalyst(9501,557).
catalyst(9502,557).
catalyst(9521,557).
catalyst(9522,557).
catalyst(9481,556).
catalyst(9482,556).
catalyst(9491,556).
catalyst(9492,556).
catalyst(9501,556).
catalyst(9502,556).
catalyst(9521,556).
catalyst(9522,556).
catalyst(9481,519).
catalyst(9482,519).
catalyst(9491,519).
catalyst(9492,519).
catalyst(9501,519).
catalyst(9502,519).
catalyst(9521,519).
catalyst(9522,519).
catalyst(9481,507).
catalyst(9482,507).
catalyst(9491,507).
catalyst(9492,507).
catalyst(9501,507).
catalyst(9502,507).
catalyst(9521,507).
catalyst(9522,507).
catalyst(9481,427).
catalyst(9482,427).
catalyst(9491,427).
catalyst(9492,427).
catalyst(9501,427).
catalyst(9502,427).
catalyst(9521,427).
catalyst(9522,427).
catalyst(9481,403).
catalyst(9482,403).
catalyst(9491,403).
catalyst(9492,403).
catalyst(9501,403).
catalyst(9502,403).
catalyst(9521,403).
catalyst(9522,403).
catalyst(9481,342).
catalyst(9482,342).
catalyst(9491,342).
catalyst(9492,342).
catalyst(9501,342).
catalyst(9502,342).
catalyst(9521,342).
catalyst(9522,342).
catalyst(9481,321).
catalyst(9482,321).
catalyst(9491,321).
catalyst(9492,321).
catalyst(9501,321).
catalyst(9502,321).
catalyst(9521,321).
catalyst(9522,321).
catalyst(9481,304).
catalyst(9482,304).
catalyst(9491,304).
catalyst(9492,304).
catalyst(9501,304).
catalyst(9502,304).
catalyst(9521,304).
catalyst(9522,304).
catalyst(9481,286).
catalyst(9482,286).
catalyst(9491,286).
catalyst(9492,286).
catalyst(9501,286).
catalyst(9502,286).
catalyst(9521,286).
catalyst(9522,286).
catalyst(9481,281).
catalyst(9482,281).
catalyst(9491,281).
catalyst(9492,281).
catalyst(9501,281).
catalyst(9502,281).
catalyst(9521,281).
catalyst(9522,281).
catalyst(9481,221).
catalyst(9482,221).
catalyst(9491,221).
catalyst(9492,221).
catalyst(9501,221).
catalyst(9502,221).
catalyst(9521,221).
catalyst(9522,221).
catalyst(9431,888).
catalyst(9432,888).
catalyst(9441,888).
catalyst(9442,888).
catalyst(9461,888).
catalyst(9462,888).
catalyst(9471,888).
catalyst(9472,888).
catalyst(9431,848).
catalyst(9432,848).
catalyst(9441,848).
catalyst(9442,848).
catalyst(9461,848).
catalyst(9462,848).
catalyst(9471,848).
catalyst(9472,848).
catalyst(9431,826).
catalyst(9432,826).
catalyst(9441,826).
catalyst(9442,826).
catalyst(9461,826).
catalyst(9462,826).
catalyst(9471,826).
catalyst(9472,826).
catalyst(9431,791).
catalyst(9432,791).
catalyst(9441,791).
catalyst(9442,791).
catalyst(9461,791).
catalyst(9462,791).
catalyst(9471,791).
catalyst(9472,791).
catalyst(9431,759).
catalyst(9432,759).
catalyst(9441,759).
catalyst(9442,759).
catalyst(9461,759).
catalyst(9462,759).
catalyst(9471,759).
catalyst(9472,759).
catalyst(9431,753).
catalyst(9432,753).
catalyst(9441,753).
catalyst(9442,753).
catalyst(9461,753).
catalyst(9462,753).
catalyst(9471,753).
catalyst(9472,753).
catalyst(9431,739).
catalyst(9432,739).
catalyst(9441,739).
catalyst(9442,739).
catalyst(9461,739).
catalyst(9462,739).
catalyst(9471,739).
catalyst(9472,739).
catalyst(9431,573).
catalyst(9432,573).
catalyst(9441,573).
catalyst(9442,573).
catalyst(9461,573).
catalyst(9462,573).
catalyst(9471,573).
catalyst(9472,573).
catalyst(9431,569).
catalyst(9432,569).
catalyst(9441,569).
catalyst(9442,569).
catalyst(9461,569).
catalyst(9462,569).
catalyst(9471,569).
catalyst(9472,569).
catalyst(9431,548).
catalyst(9432,548).
catalyst(9441,548).
catalyst(9442,548).
catalyst(9461,548).
catalyst(9462,548).
catalyst(9471,548).
catalyst(9472,548).
catalyst(9431,529).
catalyst(9432,529).
catalyst(9441,529).
catalyst(9442,529).
catalyst(9461,529).
catalyst(9462,529).
catalyst(9471,529).
catalyst(9472,529).
catalyst(9431,365).
catalyst(9432,365).
catalyst(9441,365).
catalyst(9442,365).
catalyst(9461,365).
catalyst(9462,365).
catalyst(9471,365).
catalyst(9472,365).
catalyst(9431,345).
catalyst(9432,345).
catalyst(9441,345).
catalyst(9442,345).
catalyst(9461,345).
catalyst(9462,345).
catalyst(9471,345).
catalyst(9472,345).
catalyst(9431,313).
catalyst(9432,313).
catalyst(9441,313).
catalyst(9442,313).
catalyst(9461,313).
catalyst(9462,313).
catalyst(9471,313).
catalyst(9472,313).
catalyst(9431,276).
catalyst(9432,276).
catalyst(9441,276).
catalyst(9442,276).
catalyst(9461,276).
catalyst(9462,276).
catalyst(9471,276).
catalyst(9472,276).
catalyst(9431,251).
catalyst(9432,251).
catalyst(9441,251).
catalyst(9442,251).
catalyst(9461,251).
catalyst(9462,251).
catalyst(9471,251).
catalyst(9472,251).
catalyst(9431,233).
catalyst(9432,233).
catalyst(9441,233).
catalyst(9442,233).
catalyst(9461,233).
catalyst(9462,233).
catalyst(9471,233).
catalyst(9472,233).
catalyst(9431,179).
catalyst(9432,179).
catalyst(9441,179).
catalyst(9442,179).
catalyst(9461,179).
catalyst(9462,179).
catalyst(9471,179).
catalyst(9472,179).
catalyst(7741,596).
catalyst(7742,596).
catalyst(7741,481).
catalyst(7742,481).
catalyst(6801,505).
catalyst(6802,505).
catalyst(9411,227).
catalyst(9412,227).
catalyst(6830,742).
catalyst(2240,846).
catalyst(9401,820).
catalyst(9402,820).
catalyst(2621,477).
catalyst(2622,477).
catalyst(9361,308).
catalyst(9362,308).
catalyst(9371,308).
catalyst(9372,308).
catalyst(7950,769).
catalyst(7950,510).
catalyst(7950,472).
catalyst(7950,256).
catalyst(9261,271).
catalyst(9262,271).
catalyst(9271,271).
catalyst(9272,271).
catalyst(9291,776).
catalyst(9292,776).
catalyst(9301,776).
catalyst(9302,776).
catalyst(9321,776).
catalyst(9322,776).
catalyst(9331,776).
catalyst(9332,776).
catalyst(9291,704).
catalyst(9292,704).
catalyst(9301,704).
catalyst(9302,704).
catalyst(9321,704).
catalyst(9322,704).
catalyst(9331,704).
catalyst(9332,704).
catalyst(9291,703).
catalyst(9292,703).
catalyst(9301,703).
catalyst(9302,703).
catalyst(9321,703).
catalyst(9322,703).
catalyst(9331,703).
catalyst(9332,703).
catalyst(2060,27).
catalyst(2150,23).
catalyst(7561,545).
catalyst(7562,545).
catalyst(9231,841).
catalyst(9232,841).
catalyst(9231,804).
catalyst(9232,804).
catalyst(9231,747).
catalyst(9232,747).
catalyst(9231,731).
catalyst(9232,731).
catalyst(9231,725).
catalyst(9232,725).
catalyst(9231,634).
catalyst(9232,634).
catalyst(9231,564).
catalyst(9232,564).
catalyst(9231,532).
catalyst(9232,532).
catalyst(9231,406).
catalyst(9232,406).
catalyst(9231,394).
catalyst(9232,394).
catalyst(9231,393).
catalyst(9232,393).
catalyst(9231,390).
catalyst(9232,390).
catalyst(9231,309).
catalyst(9232,309).
catalyst(9231,278).
catalyst(9232,278).
catalyst(9231,204).
catalyst(9232,204).
catalyst(9231,183).
catalyst(9232,183).
catalyst(9241,572).
catalyst(9242,572).
catalyst(7480,329).
catalyst(2670,161).
catalyst(2590,348).
catalyst(7990,680).
catalyst(7620,310).
catalyst(3810,409).
catalyst(9191,850).
catalyst(9192,850).
catalyst(9191,767).
catalyst(9192,767).
catalyst(9191,694).
catalyst(9192,694).
catalyst(9191,689).
catalyst(9192,689).
catalyst(9191,685).
catalyst(9192,685).
catalyst(9191,452).
catalyst(9192,452).
catalyst(9191,392).
catalyst(9192,392).
catalyst(9191,387).
catalyst(9192,387).
catalyst(9191,346).
catalyst(9192,346).
catalyst(9191,311).
catalyst(9192,311).
catalyst(9191,290).
catalyst(9192,290).
catalyst(9191,280).
catalyst(9192,280).
catalyst(9191,263).
catalyst(9192,263).
catalyst(9191,257).
catalyst(9192,257).
catalyst(9191,216).
catalyst(9192,216).
catalyst(9191,182).
catalyst(9192,182).
catalyst(9201,879).
catalyst(9202,879).
catalyst(9211,879).
catalyst(9212,879).
catalyst(9221,879).
catalyst(9222,879).
catalyst(9201,517).
catalyst(9202,517).
catalyst(9211,517).
catalyst(9212,517).
catalyst(9221,517).
catalyst(9222,517).
catalyst(9201,260).
catalyst(9202,260).
catalyst(9211,260).
catalyst(9212,260).
catalyst(9221,260).
catalyst(9222,260).
catalyst(9201,211).
catalyst(9202,211).
catalyst(9211,211).
catalyst(9212,211).
catalyst(9221,211).
catalyst(9222,211).
catalyst(9201,210).
catalyst(9202,210).
catalyst(9211,210).
catalyst(9212,210).
catalyst(9221,210).
catalyst(9222,210).
catalyst(3050,522).
catalyst(3050,380).
catalyst(6780,496).
catalyst(6710,172).
catalyst(4690,469).
catalyst(9181,856).
catalyst(9182,856).
catalyst(9181,718).
catalyst(9182,718).
catalyst(9201,294).
catalyst(9202,294).
catalyst(7800,559).
catalyst(5150,119).
catalyst(5160,118).
catalyst(5170,117).
catalyst(5190,116).
catalyst(5200,114).
catalyst(5210,113).
catalyst(5220,112).
catalyst(5230,111).
catalyst(5250,110).
catalyst(9161,495).
catalyst(9162,495).
catalyst(9161,494).
catalyst(9162,494).
catalyst(4340,786).
catalyst(6730,865).
catalyst(5970,831).
catalyst(5990,831).
catalyst(6010,831).
catalyst(6010,440).
catalyst(9131,626).
catalyst(9132,626).
catalyst(9141,626).
catalyst(9142,626).
catalyst(9041,422).
catalyst(9042,422).
catalyst(9071,668).
catalyst(9072,668).
catalyst(9081,668).
catalyst(9082,668).
catalyst(9051,591).
catalyst(9052,591).
catalyst(9061,591).
catalyst(9062,591).
catalyst(7650,568).
catalyst(7660,568).
catalyst(7660,566).
catalyst(7660,538).
catalyst(7660,479).
catalyst(7660,478).
catalyst(7660,237).
catalyst(7671,223).
catalyst(7672,223).
catalyst(7681,223).
catalyst(7682,223).
catalyst(7691,223).
catalyst(7692,223).
catalyst(7701,223).
catalyst(7702,223).
catalyst(7710,223).
catalyst(7720,223).
catalyst(7730,223).
catalyst(1140,535).
catalyst(7610,873).
catalyst(7610,296).
catalyst(7610,188).
catalyst(5540,340).
catalyst(2140,24).
catalyst(4490,372).
catalyst(9021,735).
catalyst(9022,735).
catalyst(4720,655).
catalyst(4720,654).
catalyst(4720,653).
catalyst(4720,652).
catalyst(4720,334).
catalyst(2031,423).
catalyst(2032,423).
catalyst(2231,423).
catalyst(2232,423).
catalyst(4880,128).
catalyst(4880,127).
catalyst(3370,327).
catalyst(3040,673).
catalyst(3040,672).
catalyst(3510,136).
catalyst(5921,683).
catalyst(5922,683).
catalyst(3900,844).
catalyst(6211,540).
catalyst(6212,540).
catalyst(6071,640).
catalyst(6072,640).
catalyst(5691,508).
catalyst(5692,508).
catalyst(5260,509).
catalyst(3850,242).
catalyst(5350,743).
catalyst(2860,220).
catalyst(8991,295).
catalyst(8992,295).
catalyst(5630,744).
catalyst(5640,744).
catalyst(5770,665).
catalyst(5780,665).
catalyst(6020,691).
catalyst(2391,467).
catalyst(2392,467).
catalyst(2401,208).
catalyst(2402,208).
catalyst(7320,551).
catalyst(4870,129).
catalyst(2580,275).
catalyst(5050,125).
catalyst(5060,123).
catalyst(7460,192).
catalyst(8831,514).
catalyst(8832,514).
catalyst(8841,514).
catalyst(8842,514).
catalyst(8821,212).
catalyst(8822,212).
catalyst(5730,230).
catalyst(3860,243).
catalyst(8851,369).
catalyst(8852,369).
catalyst(8861,369).
catalyst(8862,369).
catalyst(8871,369).
catalyst(8872,369).
catalyst(8881,369).
catalyst(8882,369).
catalyst(8891,369).
catalyst(8892,369).
catalyst(8901,369).
catalyst(8902,369).
catalyst(8931,369).
catalyst(8932,369).
catalyst(8941,369).
catalyst(8942,369).
catalyst(8951,369).
catalyst(8952,369).
catalyst(8971,369).
catalyst(8972,369).
catalyst(7380,187).
catalyst(3480,662).
catalyst(3500,662).
catalyst(2540,164).
catalyst(1870,357).
catalyst(7550,649).
catalyst(7550,642).
catalyst(7550,449).
catalyst(8791,338).
catalyst(8792,338).
catalyst(8801,338).
catalyst(8802,338).
catalyst(8811,338).
catalyst(8812,338).
catalyst(8791,268).
catalyst(8792,268).
catalyst(8801,268).
catalyst(8802,268).
catalyst(8811,268).
catalyst(8812,268).
catalyst(5030,726).
catalyst(3950,614).
catalyst(5880,360).
catalyst(6470,771).
catalyst(2300,168).
catalyst(1960,306).
catalyst(3600,619).
catalyst(8000,633).
catalyst(3941,779).
catalyst(3942,779).
catalyst(6900,456).
catalyst(8781,330).
catalyst(8782,330).
catalyst(4560,363).
catalyst(2550,768).
catalyst(8020,871).
catalyst(8020,381).
catalyst(1890,620).
catalyst(3630,620).
catalyst(1890,388).
catalyst(3630,388).
catalyst(3740,317).
catalyst(8231,869).
catalyst(8232,869).
catalyst(8231,836).
catalyst(8232,836).
catalyst(8231,732).
catalyst(8232,732).
catalyst(8231,511).
catalyst(8232,511).
catalyst(8231,473).
catalyst(8232,473).
catalyst(8061,862).
catalyst(8062,862).
catalyst(3590,421).
catalyst(4570,455).
catalyst(8181,671).
catalyst(8182,671).
catalyst(8181,565).
catalyst(8182,565).
catalyst(4191,417).
catalyst(4192,417).
catalyst(3680,760).
catalyst(7031,612).
catalyst(7032,612).
catalyst(7151,612).
catalyst(7152,612).
catalyst(5661,853).
catalyst(5662,853).
catalyst(5661,758).
catalyst(5662,758).
catalyst(5661,426).
catalyst(5662,426).
catalyst(5661,398).
catalyst(5662,398).
catalyst(1970,822).
catalyst(4580,255).
catalyst(3750,318).
catalyst(3700,430).
catalyst(8741,537).
catalyst(8742,537).
catalyst(8751,537).
catalyst(8752,537).
catalyst(4520,536).
catalyst(4520,247).
catalyst(4540,248).
catalyst(3961,488).
catalyst(3962,488).
catalyst(6051,679).
catalyst(6052,679).
catalyst(6091,679).
catalyst(6092,679).
catalyst(4500,414).
catalyst(7931,550).
catalyst(7932,550).
catalyst(7751,195).
catalyst(7752,195).
catalyst(8711,196).
catalyst(8712,196).
catalyst(8281,307).
catalyst(8282,307).
catalyst(3610,297).
catalyst(7921,801).
catalyst(7922,801).
catalyst(7841,368).
catalyst(7842,368).
catalyst(8341,224).
catalyst(8342,224).
catalyst(8351,224).
catalyst(8352,224).
catalyst(6340,416).
catalyst(6370,416).
catalyst(6461,845).
catalyst(6462,845).
catalyst(6250,59).
catalyst(8241,782).
catalyst(8242,782).
catalyst(8241,608).
catalyst(8242,608).
catalyst(8251,608).
catalyst(8252,608).
catalyst(8241,258).
catalyst(8242,258).
catalyst(7861,711).
catalyst(7862,711).
catalyst(7861,603).
catalyst(7862,603).
catalyst(4891,366).
catalyst(4892,366).
catalyst(4981,366).
catalyst(4982,366).
catalyst(3690,877).
catalyst(6410,501).
catalyst(6790,558).
catalyst(8601,476).
catalyst(8602,476).
catalyst(8611,476).
catalyst(8612,476).
catalyst(8601,457).
catalyst(8602,457).
catalyst(8611,457).
catalyst(8612,457).
catalyst(8591,487).
catalyst(8592,487).
catalyst(8591,300).
catalyst(8592,300).
catalyst(8571,843).
catalyst(8572,843).
catalyst(8581,843).
catalyst(8582,843).
catalyst(8571,635).
catalyst(8572,635).
catalyst(8581,635).
catalyst(8582,635).
catalyst(8561,881).
catalyst(8562,881).
catalyst(8561,215).
catalyst(8562,215).
catalyst(8551,491).
catalyst(8552,491).
catalyst(8551,386).
catalyst(8552,386).
catalyst(1910,778).
catalyst(1920,439).
catalyst(8531,809).
catalyst(8532,809).
catalyst(3890,503).
catalyst(3890,335).
catalyst(8671,789).
catalyst(8672,789).
catalyst(3390,328).
catalyst(8521,876).
catalyst(8522,876).
catalyst(8521,644).
catalyst(8522,644).
catalyst(8521,402).
catalyst(8522,402).
catalyst(3780,874).
catalyst(8511,489).
catalyst(8512,489).
catalyst(4730,490).
catalyst(8661,617).
catalyst(8662,617).
catalyst(8661,525).
catalyst(8662,525).
catalyst(8651,847).
catalyst(8652,847).
catalyst(8651,681).
catalyst(8652,681).
catalyst(8641,840).
catalyst(8642,840).
catalyst(8641,185).
catalyst(8642,185).
catalyst(4060,738).
catalyst(4070,302).
catalyst(8631,827).
catalyst(8632,827).
catalyst(8621,450).
catalyst(8622,450).
catalyst(8111,471).
catalyst(8112,471).
catalyst(4900,875).
catalyst(2330,530).
catalyst(2510,165).
catalyst(2461,819).
catalyst(2462,819).
catalyst(2461,713).
catalyst(2462,713).
catalyst(2461,604).
catalyst(2462,604).
catalyst(3160,549).
catalyst(6120,437).
catalyst(8491,397).
catalyst(8492,397).
catalyst(2480,167).
catalyst(2631,772).
catalyst(2632,772).
catalyst(8461,282).
catalyst(8462,282).
catalyst(8451,283).
catalyst(8452,283).
catalyst(6151,438).
catalyst(6152,438).
catalyst(8441,284).
catalyst(8442,284).
catalyst(2410,468).
catalyst(3971,783).
catalyst(3972,783).
catalyst(8481,285).
catalyst(8482,285).
catalyst(2170,502).
catalyst(6030,723).
catalyst(4760,885).
catalyst(4760,453).
catalyst(10401,823).
catalyst(10402,823).
catalyst(4000,584).
catalyst(4000,554).
catalyst(7980,425).
catalyst(7980,225).
catalyst(7060,860).
catalyst(7080,860).
catalyst(7090,860).
catalyst(7110,860).
catalyst(7120,860).
catalyst(7060,765).
catalyst(7080,765).
catalyst(7090,765).
catalyst(7110,765).
catalyst(7120,765).
catalyst(7161,765).
catalyst(7162,765).
catalyst(7060,613).
catalyst(7080,613).
catalyst(7090,613).
catalyst(7110,613).
catalyst(7120,613).
catalyst(7060,445).
catalyst(7080,445).
catalyst(7090,445).
catalyst(7110,445).
catalyst(7120,445).
catalyst(8431,795).
catalyst(8432,795).
catalyst(8431,287).
catalyst(8432,287).
catalyst(8421,546).
catalyst(8422,546).
catalyst(8411,775).
catalyst(8412,775).
catalyst(371,884).
catalyst(372,884).
catalyst(781,863).
catalyst(782,863).
catalyst(881,863).
catalyst(882,863).
catalyst(911,863).
catalyst(912,863).
catalyst(921,863).
catalyst(922,863).
catalyst(941,863).
catalyst(942,863).
catalyst(1191,863).
catalyst(1192,863).
catalyst(730,830).
catalyst(821,830).
catalyst(822,830).
catalyst(941,830).
catalyst(942,830).
catalyst(190,812).
catalyst(6570,810).
catalyst(6580,810).
catalyst(1431,805).
catalyst(1432,805).
catalyst(190,799).
catalyst(21,796).
catalyst(22,796).
catalyst(31,796).
catalyst(32,796).
catalyst(1200,794).
catalyst(1160,790).
catalyst(801,777).
catalyst(802,777).
catalyst(811,777).
catalyst(812,777).
catalyst(831,777).
catalyst(832,777).
catalyst(901,777).
catalyst(902,777).
catalyst(941,777).
catalyst(942,777).
catalyst(1200,761).
catalyst(931,754).
catalyst(932,754).
catalyst(371,745).
catalyst(372,745).
catalyst(6620,729).
catalyst(6310,720).
catalyst(1590,707).
catalyst(341,701).
catalyst(342,701).
catalyst(1540,676).
catalyst(1561,676).
catalyst(1562,676).
catalyst(6570,667).
catalyst(6580,667).
catalyst(190,663).
catalyst(251,650).
catalyst(252,650).
catalyst(6330,647).
catalyst(6360,647).
catalyst(350,646).
catalyst(1200,645).
catalyst(750,636).
catalyst(630,632).
catalyst(650,632).
catalyst(6560,628).
catalyst(781,627).
catalyst(782,627).
catalyst(791,627).
catalyst(792,627).
catalyst(801,627).
catalyst(802,627).
catalyst(811,627).
catalyst(812,627).
catalyst(821,627).
catalyst(822,627).
catalyst(831,627).
catalyst(832,627).
catalyst(841,627).
catalyst(842,627).
catalyst(861,627).
catalyst(862,627).
catalyst(871,627).
catalyst(872,627).
catalyst(881,627).
catalyst(882,627).
catalyst(901,627).
catalyst(902,627).
catalyst(911,627).
catalyst(912,627).
catalyst(921,627).
catalyst(922,627).
catalyst(931,627).
catalyst(932,627).
catalyst(941,627).
catalyst(942,627).
catalyst(1191,627).
catalyst(1192,627).
catalyst(390,622).
catalyst(1021,622).
catalyst(1022,622).
catalyst(1521,602).
catalyst(1522,602).
catalyst(6610,594).
catalyst(1250,581).
catalyst(1581,579).
catalyst(1582,579).
catalyst(1200,567).
catalyst(6560,555).
catalyst(361,552).
catalyst(362,552).
catalyst(841,483).
catalyst(842,483).
catalyst(871,461).
catalyst(872,461).
catalyst(350,454).
catalyst(371,451).
catalyst(372,451).
catalyst(111,448).
catalyst(112,448).
catalyst(841,447).
catalyst(842,447).
catalyst(581,432).
catalyst(582,432).
catalyst(590,432).
catalyst(600,432).
catalyst(781,405).
catalyst(782,405).
catalyst(911,405).
catalyst(912,405).
catalyst(1191,405).
catalyst(1192,405).
catalyst(1200,399).
catalyst(581,377).
catalyst(582,377).
catalyst(590,377).
catalyst(600,377).
catalyst(581,376).
catalyst(582,376).
catalyst(590,376).
catalyst(600,376).
catalyst(581,375).
catalyst(582,375).
catalyst(590,375).
catalyst(600,375).
catalyst(1571,374).
catalyst(1572,374).
catalyst(931,367).
catalyst(932,367).
catalyst(1191,356).
catalyst(1192,356).
catalyst(1200,356).
catalyst(781,352).
catalyst(782,352).
catalyst(841,352).
catalyst(842,352).
catalyst(881,352).
catalyst(882,352).
catalyst(901,352).
catalyst(902,352).
catalyst(921,352).
catalyst(922,352).
catalyst(6680,351).
catalyst(1160,349).
catalyst(6650,332).
catalyst(6550,331).
catalyst(791,305).
catalyst(792,305).
catalyst(801,305).
catalyst(802,305).
catalyst(811,305).
catalyst(812,305).
catalyst(831,305).
catalyst(832,305).
catalyst(841,305).
catalyst(842,305).
catalyst(861,305).
catalyst(862,305).
catalyst(901,305).
catalyst(902,305).
catalyst(690,291).
catalyst(730,291).
catalyst(241,252).
catalyst(242,252).
catalyst(781,240).
catalyst(782,240).
catalyst(791,240).
catalyst(792,240).
catalyst(801,240).
catalyst(802,240).
catalyst(831,240).
catalyst(832,240).
catalyst(841,240).
catalyst(842,240).
catalyst(861,240).
catalyst(862,240).
catalyst(871,240).
catalyst(872,240).
catalyst(881,240).
catalyst(882,240).
catalyst(921,240).
catalyst(922,240).
catalyst(941,240).
catalyst(942,240).
catalyst(1191,240).
catalyst(1192,240).
catalyst(1121,236).
catalyst(1122,236).
catalyst(350,235).
catalyst(1491,234).
catalyst(1492,234).
catalyst(1501,234).
catalyst(1502,234).
catalyst(1511,234).
catalyst(1512,234).
catalyst(1590,209).
catalyst(791,206).
catalyst(792,206).
catalyst(801,206).
catalyst(802,206).
catalyst(811,206).
catalyst(812,206).
catalyst(861,206).
catalyst(862,206).
catalyst(871,206).
catalyst(872,206).
catalyst(901,206).
catalyst(902,206).
catalyst(791,205).
catalyst(792,205).
catalyst(801,205).
catalyst(802,205).
catalyst(811,205).
catalyst(812,205).
catalyst(831,205).
catalyst(832,205).
catalyst(841,205).
catalyst(842,205).
catalyst(861,205).
catalyst(862,205).
catalyst(901,205).
catalyst(902,205).
catalyst(540,180).
catalyst(1590,178).
catalyst(2660,162).
catalyst(6960,157).
catalyst(2830,156).
catalyst(2840,155).
catalyst(2920,153).
catalyst(2920,152).
catalyst(2920,151).
catalyst(2920,150).
catalyst(2960,149).
catalyst(6970,148).
catalyst(2990,147).
catalyst(3281,145).
catalyst(3282,145).
catalyst(6970,141).
catalyst(4131,134).
catalyst(4132,134).
catalyst(6980,133).
catalyst(4940,126).
catalyst(6980,124).
catalyst(10,108).
catalyst(41,107).
catalyst(42,107).
catalyst(51,106).
catalyst(52,106).
catalyst(91,105).
catalyst(92,105).
catalyst(101,104).
catalyst(102,104).
catalyst(131,103).
catalyst(132,103).
catalyst(141,101).
catalyst(142,101).
catalyst(151,100).
catalyst(152,100).
catalyst(230,99).
catalyst(261,98).
catalyst(262,98).
catalyst(321,96).
catalyst(322,96).
catalyst(401,95).
catalyst(402,95).
catalyst(451,94).
catalyst(452,94).
catalyst(460,93).
catalyst(490,90).
catalyst(510,89).
catalyst(530,88).
catalyst(550,87).
catalyst(560,86).
catalyst(460,85).
catalyst(510,83).
catalyst(530,82).
catalyst(560,81).
catalyst(460,80).
catalyst(490,79).
catalyst(510,77).
catalyst(530,76).
catalyst(550,75).
catalyst(560,74).
catalyst(670,73).
catalyst(970,71).
catalyst(980,70).
catalyst(990,69).
catalyst(1000,68).
catalyst(1010,67).
catalyst(1041,66).
catalyst(1042,66).
catalyst(1050,65).
catalyst(1111,64).
catalyst(1112,64).
catalyst(1130,63).
catalyst(1150,62).
catalyst(1220,61).
catalyst(1261,60).
catalyst(1262,60).
catalyst(1291,58).
catalyst(1292,58).
catalyst(1301,57).
catalyst(1302,57).
catalyst(1311,56).
catalyst(1312,56).
catalyst(1321,55).
catalyst(1322,55).
catalyst(1331,54).
catalyst(1332,54).
catalyst(1341,53).
catalyst(1342,53).
catalyst(1351,52).
catalyst(1352,52).
catalyst(6260,51).
catalyst(1371,50).
catalyst(1372,50).
catalyst(1381,49).
catalyst(1382,49).
catalyst(1411,48).
catalyst(1412,48).
catalyst(1451,47).
catalyst(1452,47).
catalyst(1531,46).
catalyst(1532,46).
catalyst(6270,45).
catalyst(1611,44).
catalyst(1612,44).
catalyst(1641,43).
catalyst(1642,43).
catalyst(1671,42).
catalyst(1672,42).
catalyst(1681,41).
catalyst(1682,41).
catalyst(1691,40).
catalyst(1692,40).
catalyst(1701,39).
catalyst(1702,39).
catalyst(1721,38).
catalyst(1722,38).
catalyst(1731,37).
catalyst(1732,37).
catalyst(1741,36).
catalyst(1742,36).
catalyst(1751,35).
catalyst(1752,35).
catalyst(1771,34).
catalyst(1772,34).
catalyst(1781,33).
catalyst(1782,33).
catalyst(1791,32).
catalyst(1792,32).
catalyst(6640,31).
catalyst(1801,30).
catalyst(1802,30).
catalyst(30050,17).
catalyst(30070,16).
catalyst(30040,15).
catalyst(10920,14).
catalyst(30060,13).
catalyst(30030,12).
catalyst(30160,11).
catalyst(30020,10).
catalyst(30010,9).
catalyst(30150,8).
catalyst(30140,7).
catalyst(30130,6).
catalyst(30120,5).
catalyst(30110,4).
catalyst(30100,3).
catalyst(30090,2).
catalyst(30080,1).

unknown_enzyme(unknown).


certain_enzyme(756).
certain_enzyme(643).
certain_enzyme(624).
certain_enzyme(709).
certain_enzyme(857).
certain_enzyme(130).
certain_enzyme(218).
certain_enzyme(219).
certain_enzyme(592).
certain_enzyme(415).
certain_enzyme(498).
certain_enzyme(693).
certain_enzyme(684).
certain_enzyme(518).
certain_enzyme(176).
certain_enzyme(175).
certain_enzyme(241).
certain_enzyme(314).
certain_enzyme(588).
certain_enzyme(696).
certain_enzyme(687).
certain_enzyme(599).
certain_enzyme(806).
certain_enzyme(733).
certain_enzyme(657).
certain_enzyme(266).
certain_enzyme(512).
certain_enzyme(475).
certain_enzyme(749).
certain_enzyme(784).
certain_enzyme(259).
certain_enzyme(239).
certain_enzyme(678).
certain_enzyme(524).
certain_enzyme(385).
certain_enzyme(692).
certain_enzyme(531).
certain_enzyme(892).
certain_enzyme(798).
certain_enzyme(561).
certain_enzyme(484).
certain_enzyme(460).
certain_enzyme(411).
certain_enzyme(361).
certain_enzyme(353).
certain_enzyme(181).
certain_enzyme(19).
certain_enzyme(629).
certain_enzyme(595).
certain_enzyme(541).
certain_enzyme(228).
certain_enzyme(580).
certain_enzyme(140).
certain_enzyme(28).
certain_enzyme(474).
certain_enzyme(29).
certain_enzyme(186).
certain_enzyme(706).
certain_enzyme(485).
certain_enzyme(341).
certain_enzyme(424).
certain_enzyme(582).
certain_enzyme(486).
certain_enzyme(543).
certain_enzyme(523).
certain_enzyme(459).
certain_enzyme(383).
certain_enzyme(122).
certain_enzyme(121).
certain_enzyme(120).
certain_enzyme(322).
certain_enzyme(570).
certain_enzyme(544).
certain_enzyme(462).
certain_enzyme(191).
certain_enzyme(868).
certain_enzyme(867).
certain_enzyme(835).
certain_enzyme(832).
certain_enzyme(384).
certain_enzyme(146).
certain_enzyme(431).
certain_enzyme(213).
certain_enzyme(137).
certain_enzyme(382).
certain_enzyme(825).
certain_enzyme(115).
certain_enzyme(396).
certain_enzyme(226).
certain_enzyme(528).
certain_enzyme(222).
certain_enzyme(757).
certain_enzyme(418).
certain_enzyme(611).
certain_enzyme(139).
certain_enzyme(621).
certain_enzyme(303).
certain_enzyme(370).
certain_enzyme(625).
certain_enzyme(533).
certain_enzyme(436).
certain_enzyme(605).
certain_enzyme(575).
certain_enzyme(364).
certain_enzyme(288).
certain_enzyme(833).
certain_enzyme(292).
certain_enzyme(174).
certain_enzyme(171).
certain_enzyme(22).
certain_enzyme(201).
certain_enzyme(719).
certain_enzyme(138).
certain_enzyme(631).
certain_enzyme(839).
certain_enzyme(428).
certain_enzyme(818).
certain_enzyme(466).
certain_enzyme(207).
certain_enzyme(651).
certain_enzyme(144).
certain_enzyme(142).
certain_enzyme(499).
certain_enzyme(607).
certain_enzyme(521).
certain_enzyme(493).
certain_enzyme(816).
certain_enzyme(715).
certain_enzyme(699).
certain_enzyme(615).
certain_enzyme(597).
certain_enzyme(378).
certain_enzyme(269).
certain_enzyme(203).
certain_enzyme(716).
certain_enzyme(700).
certain_enzyme(616).
certain_enzyme(270).
certain_enzyme(410).
certain_enzyme(838).
certain_enzyme(401).
certain_enzyme(842).
certain_enzyme(336).
certain_enzyme(371).
certain_enzyme(887).
certain_enzyme(587).
certain_enzyme(736).
certain_enzyme(727).
certain_enzyme(682).
certain_enzyme(641).
certain_enzyme(527).
certain_enzyme(497).
certain_enzyme(434).
certain_enzyme(433).
certain_enzyme(267).
certain_enzyme(21).
certain_enzyme(20).
certain_enzyme(18).
certain_enzyme(864).
certain_enzyme(200).
certain_enzyme(866).
certain_enzyme(637).
certain_enzyme(344).
certain_enzyme(630).
certain_enzyme(787).
certain_enzyme(131).
certain_enzyme(389).
certain_enzyme(578).
certain_enzyme(688).
certain_enzyme(261).
certain_enzyme(788).
certain_enzyme(656).
certain_enzyme(232).
certain_enzyme(299).
certain_enzyme(343).
certain_enzyme(714).
certain_enzyme(639).
certain_enzyme(177).
certain_enzyme(553).
certain_enzyme(547).
certain_enzyme(880).
certain_enzyme(214).
certain_enzyme(677).
certain_enzyme(446).
certain_enzyme(712).
certain_enzyme(238).
certain_enzyme(708).
certain_enzyme(737).
certain_enzyme(534).
certain_enzyme(766).
certain_enzyme(254).
certain_enzyme(132).
certain_enzyme(755).
certain_enzyme(325).
certain_enzyme(400).
certain_enzyme(858).
certain_enzyme(379).
certain_enzyme(163).
certain_enzyme(837).
certain_enzyme(264).
certain_enzyme(166).
certain_enzyme(320).
certain_enzyme(834).
certain_enzyme(458).
certain_enzyme(859).
certain_enzyme(659).
certain_enzyme(669).
certain_enzyme(419).
certain_enzyme(870).
certain_enzyme(762).
certain_enzyme(249).
certain_enzyme(702).
certain_enzyme(289).
certain_enzyme(279).
certain_enzyme(741).
certain_enzyme(539).
certain_enzyme(886).
certain_enzyme(824).
certain_enzyme(589).
certain_enzyme(464).
certain_enzyme(274).
certain_enzyme(273).
certain_enzyme(173).
certain_enzyme(666).
certain_enzyme(407).
certain_enzyme(855).
certain_enzyme(802).
certain_enzyme(800).
certain_enzyme(717).
certain_enzyme(690).
certain_enzyme(542).
certain_enzyme(358).
certain_enzyme(293).
certain_enzyme(245).
certain_enzyme(734).
certain_enzyme(526).
certain_enzyme(728).
certain_enzyme(698).
certain_enzyme(217).
certain_enzyme(748).
certain_enzyme(202).
certain_enzyme(198).
certain_enzyme(359).
certain_enzyme(660).
certain_enzyme(26).
certain_enzyme(25).
certain_enzyme(814).
certain_enzyme(730).
certain_enzyme(337).
certain_enzyme(412).
certain_enzyme(586).
certain_enzyme(109).
certain_enzyme(661).
certain_enzyme(339).
certain_enzyme(889).
certain_enzyme(849).
certain_enzyme(770).
certain_enzyme(710).
certain_enzyme(272).
certain_enzyme(190).
certain_enzyme(189).
certain_enzyme(562).
certain_enzyme(563).
certain_enzyme(751).
certain_enzyme(878).
certain_enzyme(315).
certain_enzyme(513).
certain_enzyme(500).
certain_enzyme(670).
certain_enzyme(443).
certain_enzyme(697).
certain_enzyme(585).
certain_enzyme(301).
certain_enzyme(229).
certain_enzyme(658).
certain_enzyme(350).
certain_enzyme(821).
certain_enzyme(793).
certain_enzyme(231).
certain_enzyme(506).
certain_enzyme(435).
certain_enzyme(638).
certain_enzyme(601).
certain_enzyme(792).
certain_enzyme(686).
certain_enzyme(600).
certain_enzyme(444).
certain_enzyme(312).
certain_enzyme(143).
certain_enzyme(135).
certain_enzyme(590).
certain_enzyme(516).
certain_enzyme(811).
certain_enzyme(773).
certain_enzyme(441).
certain_enzyme(413).
certain_enzyme(705).
certain_enzyme(721).
certain_enzyme(470).
certain_enzyme(664).
certain_enzyme(618).
certain_enzyme(577).
certain_enzyme(253).
certain_enzyme(463).
certain_enzyme(244).
certain_enzyme(583).
certain_enzyme(72).
certain_enzyme(851).
certain_enzyme(574).
certain_enzyme(362).
certain_enzyme(170).
certain_enzyme(593).
certain_enzyme(326).
certain_enzyme(695).
certain_enzyme(404).
certain_enzyme(482).
certain_enzyme(648).
certain_enzyme(355).
certain_enzyme(160).
certain_enzyme(159).
certain_enzyme(158).
certain_enzyme(722).
certain_enzyme(852).
certain_enzyme(797).
certain_enzyme(609).
certain_enzyme(560).
certain_enzyme(520).
certain_enzyme(515).
certain_enzyme(504).
certain_enzyme(420).
certain_enzyme(492).
certain_enzyme(764).
certain_enzyme(883).
certain_enzyme(861).
certain_enzyme(780).
certain_enzyme(854).
certain_enzyme(92).
certain_enzyme(298).
certain_enzyme(197).
certain_enzyme(408).
certain_enzyme(323).
certain_enzyme(316).
certain_enzyme(102).
certain_enzyme(97).
certain_enzyme(319).
certain_enzyme(333).
certain_enzyme(250).
certain_enzyme(373).
certain_enzyme(91).
certain_enzyme(84).
certain_enzyme(78).
certain_enzyme(154).
certain_enzyme(724).
certain_enzyme(395).
certain_enzyme(324).
certain_enzyme(598).
certain_enzyme(781).
certain_enzyme(347).
certain_enzyme(785).
certain_enzyme(610).
certain_enzyme(480).
certain_enzyme(391).
certain_enzyme(184).
certain_enzyme(807).
certain_enzyme(752).
certain_enzyme(674).
certain_enzyme(193).
certain_enzyme(194).
certain_enzyme(265).
certain_enzyme(442).
certain_enzyme(465).
certain_enzyme(675).
certain_enzyme(623).
certain_enzyme(262).
certain_enzyme(277).
certain_enzyme(169).
certain_enzyme(571).
certain_enzyme(199).
certain_enzyme(429).
certain_enzyme(354).
certain_enzyme(246).
certain_enzyme(891).
certain_enzyme(890).
certain_enzyme(882).
certain_enzyme(872).
certain_enzyme(829).
certain_enzyme(828).
certain_enzyme(817).
certain_enzyme(815).
certain_enzyme(813).
certain_enzyme(808).
certain_enzyme(803).
certain_enzyme(774).
certain_enzyme(763).
certain_enzyme(750).
certain_enzyme(746).
certain_enzyme(740).
certain_enzyme(606).
certain_enzyme(576).
certain_enzyme(557).
certain_enzyme(556).
certain_enzyme(519).
certain_enzyme(507).
certain_enzyme(427).
certain_enzyme(403).
certain_enzyme(342).
certain_enzyme(321).
certain_enzyme(304).
certain_enzyme(286).
certain_enzyme(281).
certain_enzyme(221).
certain_enzyme(888).
certain_enzyme(848).
certain_enzyme(826).
certain_enzyme(791).
certain_enzyme(759).
certain_enzyme(753).
certain_enzyme(739).
certain_enzyme(573).
certain_enzyme(569).
certain_enzyme(548).
certain_enzyme(529).
certain_enzyme(365).
certain_enzyme(345).
certain_enzyme(313).
certain_enzyme(276).
certain_enzyme(251).
certain_enzyme(233).
certain_enzyme(179).
certain_enzyme(596).
certain_enzyme(481).
certain_enzyme(505).
certain_enzyme(227).
certain_enzyme(742).
certain_enzyme(846).
certain_enzyme(820).
certain_enzyme(477).
certain_enzyme(308).
certain_enzyme(769).
certain_enzyme(510).
certain_enzyme(472).
certain_enzyme(256).
certain_enzyme(271).
certain_enzyme(776).
certain_enzyme(704).
certain_enzyme(703).
certain_enzyme(27).
certain_enzyme(23).
certain_enzyme(545).
certain_enzyme(841).
certain_enzyme(804).
certain_enzyme(747).
certain_enzyme(731).
certain_enzyme(725).
certain_enzyme(634).
certain_enzyme(564).
certain_enzyme(532).
certain_enzyme(406).
certain_enzyme(394).
certain_enzyme(393).
certain_enzyme(390).
certain_enzyme(309).
certain_enzyme(278).
certain_enzyme(204).
certain_enzyme(183).
certain_enzyme(572).
certain_enzyme(329).
certain_enzyme(161).
certain_enzyme(348).
certain_enzyme(680).
certain_enzyme(310).
certain_enzyme(409).
certain_enzyme(850).
certain_enzyme(767).
certain_enzyme(694).
certain_enzyme(689).
certain_enzyme(685).
certain_enzyme(452).
certain_enzyme(392).
certain_enzyme(387).
certain_enzyme(346).
certain_enzyme(311).
certain_enzyme(290).
certain_enzyme(280).
certain_enzyme(263).
certain_enzyme(257).
certain_enzyme(216).
certain_enzyme(182).
certain_enzyme(879).
certain_enzyme(517).
certain_enzyme(260).
certain_enzyme(211).
certain_enzyme(210).
certain_enzyme(522).
certain_enzyme(380).
certain_enzyme(496).
certain_enzyme(172).
certain_enzyme(469).
certain_enzyme(856).
certain_enzyme(718).
certain_enzyme(294).
certain_enzyme(559).
certain_enzyme(119).
certain_enzyme(118).
certain_enzyme(117).
certain_enzyme(116).
certain_enzyme(114).
certain_enzyme(113).
certain_enzyme(112).
certain_enzyme(111).
certain_enzyme(110).
certain_enzyme(495).
certain_enzyme(494).
certain_enzyme(786).
certain_enzyme(865).
certain_enzyme(831).
certain_enzyme(440).
certain_enzyme(626).
certain_enzyme(422).
certain_enzyme(668).
certain_enzyme(591).
certain_enzyme(568).
certain_enzyme(566).
certain_enzyme(538).
certain_enzyme(479).
certain_enzyme(478).
certain_enzyme(237).
certain_enzyme(223).
certain_enzyme(535).
certain_enzyme(873).
certain_enzyme(296).
certain_enzyme(188).
certain_enzyme(340).
certain_enzyme(24).
certain_enzyme(372).
certain_enzyme(735).
certain_enzyme(655).
certain_enzyme(654).
certain_enzyme(653).
certain_enzyme(652).
certain_enzyme(334).
certain_enzyme(423).
certain_enzyme(128).
certain_enzyme(127).
certain_enzyme(327).
certain_enzyme(673).
certain_enzyme(672).
certain_enzyme(136).
certain_enzyme(683).
certain_enzyme(844).
certain_enzyme(540).
certain_enzyme(640).
certain_enzyme(508).
certain_enzyme(509).
certain_enzyme(242).
certain_enzyme(743).
certain_enzyme(220).
certain_enzyme(295).
certain_enzyme(744).
certain_enzyme(665).
certain_enzyme(691).
certain_enzyme(467).
certain_enzyme(208).
certain_enzyme(551).
certain_enzyme(129).
certain_enzyme(275).
certain_enzyme(125).
certain_enzyme(123).
certain_enzyme(192).
certain_enzyme(514).
certain_enzyme(212).
certain_enzyme(230).
certain_enzyme(243).
certain_enzyme(369).
certain_enzyme(187).
certain_enzyme(662).
certain_enzyme(164).
certain_enzyme(357).
certain_enzyme(649).
certain_enzyme(642).
certain_enzyme(449).
certain_enzyme(338).
certain_enzyme(268).
certain_enzyme(726).
certain_enzyme(614).
certain_enzyme(360).
certain_enzyme(771).
certain_enzyme(168).
certain_enzyme(306).
certain_enzyme(619).
certain_enzyme(633).
certain_enzyme(779).
certain_enzyme(456).
certain_enzyme(330).
certain_enzyme(363).
certain_enzyme(768).
certain_enzyme(871).
certain_enzyme(381).
certain_enzyme(620).
certain_enzyme(388).
certain_enzyme(317).
certain_enzyme(869).
certain_enzyme(836).
certain_enzyme(732).
certain_enzyme(511).
certain_enzyme(473).
certain_enzyme(862).
certain_enzyme(421).
certain_enzyme(455).
certain_enzyme(671).
certain_enzyme(565).
certain_enzyme(417).
certain_enzyme(760).
certain_enzyme(612).
certain_enzyme(853).
certain_enzyme(758).
certain_enzyme(426).
certain_enzyme(398).
certain_enzyme(822).
certain_enzyme(255).
certain_enzyme(318).
certain_enzyme(430).
certain_enzyme(537).
certain_enzyme(536).
certain_enzyme(247).
certain_enzyme(248).
certain_enzyme(488).
certain_enzyme(679).
certain_enzyme(414).
certain_enzyme(550).
certain_enzyme(195).
certain_enzyme(196).
certain_enzyme(307).
certain_enzyme(297).
certain_enzyme(801).
certain_enzyme(368).
certain_enzyme(224).
certain_enzyme(416).
certain_enzyme(845).
certain_enzyme(59).
certain_enzyme(782).
certain_enzyme(608).
certain_enzyme(258).
certain_enzyme(711).
certain_enzyme(603).
certain_enzyme(366).
certain_enzyme(877).
certain_enzyme(501).
certain_enzyme(558).
certain_enzyme(476).
certain_enzyme(457).
certain_enzyme(487).
certain_enzyme(300).
certain_enzyme(843).
certain_enzyme(635).
certain_enzyme(881).
certain_enzyme(215).
certain_enzyme(491).
certain_enzyme(386).
certain_enzyme(778).
certain_enzyme(439).
certain_enzyme(809).
certain_enzyme(503).
certain_enzyme(335).
certain_enzyme(789).
certain_enzyme(328).
certain_enzyme(876).
certain_enzyme(644).
certain_enzyme(402).
certain_enzyme(874).
certain_enzyme(489).
certain_enzyme(490).
certain_enzyme(617).
certain_enzyme(525).
certain_enzyme(847).
certain_enzyme(681).
certain_enzyme(840).
certain_enzyme(185).
certain_enzyme(738).
certain_enzyme(302).
certain_enzyme(827).
certain_enzyme(450).
certain_enzyme(471).
certain_enzyme(875).
certain_enzyme(530).
certain_enzyme(165).
certain_enzyme(819).
certain_enzyme(713).
certain_enzyme(604).
certain_enzyme(549).
certain_enzyme(437).
certain_enzyme(397).
certain_enzyme(167).
certain_enzyme(772).
certain_enzyme(282).
certain_enzyme(283).
certain_enzyme(438).
certain_enzyme(284).
certain_enzyme(468).
certain_enzyme(783).
certain_enzyme(285).
certain_enzyme(502).
certain_enzyme(723).
certain_enzyme(885).
certain_enzyme(453).
certain_enzyme(823).
certain_enzyme(584).
certain_enzyme(554).
certain_enzyme(425).
certain_enzyme(225).
certain_enzyme(860).
certain_enzyme(765).
certain_enzyme(613).
certain_enzyme(445).
certain_enzyme(795).
certain_enzyme(287).
certain_enzyme(546).
certain_enzyme(775).
certain_enzyme(884).
certain_enzyme(863).
certain_enzyme(830).
certain_enzyme(812).
certain_enzyme(810).
certain_enzyme(805).
certain_enzyme(799).
certain_enzyme(796).
certain_enzyme(794).
certain_enzyme(790).
certain_enzyme(777).
certain_enzyme(761).
certain_enzyme(754).
certain_enzyme(745).
certain_enzyme(729).
certain_enzyme(720).
certain_enzyme(707).
certain_enzyme(701).
certain_enzyme(676).
certain_enzyme(667).
certain_enzyme(663).
certain_enzyme(650).
certain_enzyme(647).
certain_enzyme(646).
certain_enzyme(645).
certain_enzyme(636).
certain_enzyme(632).
certain_enzyme(628).
certain_enzyme(627).
certain_enzyme(622).
certain_enzyme(602).
certain_enzyme(594).
certain_enzyme(581).
certain_enzyme(579).
certain_enzyme(567).
certain_enzyme(555).
certain_enzyme(552).
certain_enzyme(483).
certain_enzyme(461).
certain_enzyme(454).
certain_enzyme(451).
certain_enzyme(448).
certain_enzyme(447).
certain_enzyme(432).
certain_enzyme(405).
certain_enzyme(399).
certain_enzyme(377).
certain_enzyme(376).
certain_enzyme(375).
certain_enzyme(374).
certain_enzyme(367).
certain_enzyme(356).
certain_enzyme(352).
certain_enzyme(351).
certain_enzyme(349).
certain_enzyme(332).
certain_enzyme(331).
certain_enzyme(305).
certain_enzyme(291).
certain_enzyme(252).
certain_enzyme(240).
certain_enzyme(236).
certain_enzyme(235).
certain_enzyme(234).
certain_enzyme(209).
certain_enzyme(206).
certain_enzyme(205).
certain_enzyme(180).
certain_enzyme(178).
certain_enzyme(162).
certain_enzyme(157).
certain_enzyme(156).
certain_enzyme(155).
certain_enzyme(153).
certain_enzyme(152).
certain_enzyme(151).
certain_enzyme(150).
certain_enzyme(149).
certain_enzyme(148).
certain_enzyme(147).
certain_enzyme(145).
certain_enzyme(141).
certain_enzyme(134).
certain_enzyme(133).
certain_enzyme(126).
certain_enzyme(124).
certain_enzyme(108).
certain_enzyme(107).
certain_enzyme(106).
certain_enzyme(105).
certain_enzyme(104).
certain_enzyme(103).
certain_enzyme(101).
certain_enzyme(100).
certain_enzyme(99).
certain_enzyme(98).
certain_enzyme(96).
certain_enzyme(95).
certain_enzyme(94).
certain_enzyme(93).
certain_enzyme(90).
certain_enzyme(89).
certain_enzyme(88).
certain_enzyme(87).
certain_enzyme(86).
certain_enzyme(85).
certain_enzyme(83).
certain_enzyme(82).
certain_enzyme(81).
certain_enzyme(80).
certain_enzyme(79).
certain_enzyme(77).
certain_enzyme(76).
certain_enzyme(75).
certain_enzyme(74).
certain_enzyme(73).
certain_enzyme(71).
certain_enzyme(70).
certain_enzyme(69).
certain_enzyme(68).
certain_enzyme(67).
certain_enzyme(66).
certain_enzyme(65).
certain_enzyme(64).
certain_enzyme(63).
certain_enzyme(62).
certain_enzyme(61).
certain_enzyme(60).
certain_enzyme(58).
certain_enzyme(57).
certain_enzyme(56).
certain_enzyme(55).
certain_enzyme(54).
certain_enzyme(53).
certain_enzyme(52).
certain_enzyme(51).
certain_enzyme(50).
certain_enzyme(49).
certain_enzyme(48).
certain_enzyme(47).
certain_enzyme(46).
certain_enzyme(45).
certain_enzyme(44).
certain_enzyme(43).
certain_enzyme(42).
certain_enzyme(41).
certain_enzyme(40).
certain_enzyme(39).
certain_enzyme(38).
certain_enzyme(37).
certain_enzyme(36).
certain_enzyme(35).
certain_enzyme(34).
certain_enzyme(33).
certain_enzyme(32).
certain_enzyme(31).
certain_enzyme(30).
certain_enzyme(17).
certain_enzyme(16).
certain_enzyme(15).
certain_enzyme(14).
certain_enzyme(13).
certain_enzyme(12).
certain_enzyme(11).
certain_enzyme(10).
certain_enzyme(9).
certain_enzyme(8).
certain_enzyme(7).
certain_enzyme(6).
certain_enzyme(5).
certain_enzyme(4).
certain_enzyme(3).
certain_enzyme(2).
certain_enzyme(1).


enzymeID(E) :- unknown_enzyme(E).
enzymeID(E) :- modifiable_enzyme(E).
enzymeID(E) :- certain_enzyme(E).

metabolite("23DAACP").
metabolite("2HDACP").
metabolite("2N6H").
metabolite("2NPMB").
metabolite("2NPMMB").
metabolite("2NPMP").
metabolite("2NPPP").
metabolite("3OACP").
metabolite("A6RP").
metabolite("ABUT").
metabolite("AT3P2").
metabolite("C00001").
metabolite("C00002").
metabolite("C00003").
metabolite("C00004").
metabolite("C00005").
metabolite("C00006").
metabolite("C00007").
metabolite("C00008").
metabolite("C00009").
metabolite("C00010").
metabolite("C00011").
metabolite("C00012").
metabolite("C00013").
metabolite("C00014").
metabolite("C00015").
metabolite("C00016").
metabolite("C00017").
metabolite("C00018").
metabolite("C00019").
metabolite("C00020").
metabolite("C00021").
metabolite("C00022").
metabolite("C00024").
metabolite("C00025").
metabolite("C00026").
metabolite("C00027").
metabolite("C00028").
metabolite("C00029").
metabolite("C00030").
metabolite("C00033").
metabolite("C00035").
metabolite("C00036").
metabolite("C00037").
metabolite("C00039").
metabolite("C00040").
metabolite("C00041").
metabolite("C00042").
metabolite("C00043").
metabolite("C00044").
metabolite("C00046").
metabolite("C00047").
metabolite("C00048").
metabolite("C00049").
metabolite("C00051").
metabolite("C00052").
metabolite("C00053").
metabolite("C00054").
metabolite("C00055").
metabolite("C00058").
metabolite("C00059").
metabolite("C00060").
metabolite("C00061").
metabolite("C00062").
metabolite("C00063").
metabolite("C00064").
metabolite("C00065").
metabolite("C00066").
metabolite("C00068").
metabolite("C00069").
metabolite("C00071").
metabolite("C00073").
metabolite("C00074").
metabolite("C00075").
metabolite("C00077").
metabolite("C00078").
metabolite("C00079").
metabolite("C00080").
metabolite("C00081").
metabolite("C00082").
metabolite("C00083").
metabolite("C00084").
metabolite("C00086").
metabolite("C00089").
metabolite("C00091").
metabolite("C00093").
metabolite("C00094").
metabolite("C00095").
metabolite("C00096").
metabolite("C00097").
metabolite("C00099").
metabolite("C00101").
metabolite("C00103").
metabolite("C00104").
metabolite("C00105").
metabolite("C00106").
metabolite("C00107").
metabolite("C00108").
metabolite("C00109").
metabolite("C00110").
metabolite("C00111").
metabolite("C00112").
metabolite("C00114").
metabolite("C00116").
metabolite("C00117").
metabolite("C00118").
metabolite("C00119").
metabolite("C00120").
metabolite("C00121").
metabolite("C00122").
metabolite("C00123").
metabolite("C00124").
metabolite("C00125").
metabolite("C00126").
metabolite("C00127").
metabolite("C00129").
metabolite("C00130").
metabolite("C00131").
metabolite("C00134").
metabolite("C00135").
metabolite("C00137").
metabolite("C00140").
metabolite("C00141").
metabolite("C00143").
metabolite("C00144").
metabolite("C00145").
metabolite("C00147").
metabolite("C00148").
metabolite("C00152").
metabolite("C00153").
metabolite("C00154").
metabolite("C00155").
metabolite("C00156").
metabolite("C00157").
metabolite("C00158").
metabolite("C00161").
metabolite("C00162").
metabolite("C00165").
metabolite("C00166").
metabolite("C00169").
metabolite("C00170").
metabolite("C00173").
metabolite("C00178").
metabolite("C00182").
metabolite("C00183").
metabolite("C00184").
metabolite("C00186").
metabolite("C00187").
metabolite("C00188").
metabolite("C00189").
metabolite("C00197").
metabolite("C00199").
metabolite("C00201").
metabolite("C00206").
metabolite("C00208").
metabolite("C00212").
metabolite("C00214").
metabolite("C00216").
metabolite("C00221").
metabolite("C00224").
metabolite("C00229").
metabolite("C00232").
metabolite("C00234").
metabolite("C00235").
metabolite("C00236").
metabolite("C00238").
metabolite("C00239").
metabolite("C00242").
metabolite("C00248").
metabolite("C00249").
metabolite("C00250").
metabolite("C00251").
metabolite("C00253").
metabolite("C00254").
metabolite("C00255").
metabolite("C00256").
metabolite("C00262").
metabolite("C00263").
metabolite("C00264").
metabolite("C00267").
metabolite("C00269").
metabolite("C00275").
metabolite("C00279").
metabolite("C00280").
metabolite("C00281").
metabolite("C00283").
metabolite("C00286").
metabolite("C00288").
metabolite("C00294").
metabolite("C00295").
metabolite("C00297").
metabolite("C00299").
metabolite("C00301").
metabolite("C00307").
metabolite("C00310").
metabolite("C00311").
metabolite("C00314").
metabolite("C00315").
metabolite("C00320").
metabolite("C00322").
metabolite("C00327").
metabolite("C00328").
metabolite("C00330").
metabolite("C00332").
metabolite("C00333").
metabolite("C00334").
metabolite("C00337").
metabolite("C00341").
metabolite("C00342").
metabolite("C00343").
metabolite("C00344").
metabolite("C00345").
metabolite("C00346").
metabolite("C00350").
metabolite("C00352").
metabolite("C00354").
metabolite("C00356").
metabolite("C00357").
metabolite("C00360").
metabolite("C00361").
metabolite("C00362").
metabolite("C00363").
metabolite("C00364").
metabolite("C00365").
metabolite("C00378").
metabolite("C00380").
metabolite("C00381").
metabolite("C00383").
metabolite("C00385").
metabolite("C00387").
metabolite("C00390").
metabolite("C00392").
metabolite("C00399").
metabolite("C00407").
metabolite("C00410").
metabolite("C00412").
metabolite("C00415").
metabolite("C00416").
metabolite("C00418").
metabolite("C00419").
metabolite("C00422").
metabolite("C00424").
metabolite("C00430").
metabolite("C00437").
metabolite("C00438").
metabolite("C00440").
metabolite("C00441").
metabolite("C00442").
metabolite("C00445").
metabolite("C00446").
metabolite("C00447").
metabolite("C00448").
metabolite("C00458").
metabolite("C00459").
metabolite("C00460").
metabolite("C00461").
metabolite("C00463").
metabolite("C00464").
metabolite("C00469").
metabolite("C00470").
metabolite("C00472").
metabolite("C00475").
metabolite("C00492").
metabolite("C00493").
metabolite("C00496").
metabolite("C00510").
metabolite("C00517").
metabolite("C00522").
metabolite("C00526").
metabolite("C00534").
metabolite("C00535").
metabolite("C00542").
metabolite("C00544").
metabolite("C00555").
metabolite("C00559").
metabolite("C00562").
metabolite("C00568").
metabolite("C00570").
metabolite("C00575").
metabolite("C00579").
metabolite("C00588").
metabolite("C00603").
metabolite("C00612").
metabolite("C00620").
metabolite("C00621").
metabolite("C00624").
metabolite("C00627").
metabolite("C00631").
metabolite("C00632").
metabolite("C00640").
metabolite("C00641").
metabolite("C00647").
metabolite("C00652").
metabolite("C00655").
metabolite("C00661").
metabolite("C00665").
metabolite("C00668").
metabolite("C00669").
metabolite("C00670").
metabolite("C00673").
metabolite("C00677").
metabolite("C00685").
metabolite("C00689").
metabolite("C00704").
metabolite("C00705").
metabolite("C00711").
metabolite("C00734").
metabolite("C00735").
metabolite("C00750").
metabolite("C00751").
metabolite("C00794").
metabolite("C00836").
metabolite("C00857").
metabolite("C00860").
metabolite("C00864").
metabolite("C00870").
metabolite("C00881").
metabolite("C00882").
metabolite("C00886").
metabolite("C00890").
metabolite("C00900").
metabolite("C00909").
metabolite("C00921").
metabolite("C00936").
metabolite("C00941").
metabolite("C00943").
metabolite("C00944").
metabolite("C00954").
metabolite("C00956").
metabolite("C00966").
metabolite("C00979").
metabolite("C00986").
metabolite("C00996").
metabolite("C00999").
metabolite("C01005").
metabolite("C01024").
metabolite("C01031").
metabolite("C01037").
metabolite("C01051").
metabolite("C01054").
metabolite("C01063").
metabolite("C01077").
metabolite("C01079").
metabolite("C01081").
metabolite("C01083").
metabolite("C01092").
metabolite("C01094").
metabolite("C01100").
metabolite("C01102").
metabolite("C01103").
metabolite("C01107").
metabolite("C01118").
metabolite("C01120").
metabolite("C01134").
metabolite("C01136").
metabolite("C01137").
metabolite("C01143").
metabolite("C01152").
metabolite("C01153").
metabolite("C01159").
metabolite("C01165").
metabolite("C01168").
metabolite("C01169").
metabolite("C01172").
metabolite("C01176").
metabolite("C01177").
metabolite("C01178").
metabolite("C01179").
metabolite("C01185").
metabolite("C01194").
metabolite("C01203").
metabolite("C01209").
metabolite("C01227").
metabolite("C01228").
metabolite("C01235").
metabolite("C01236").
metabolite("C01241").
metabolite("C01242").
metabolite("C01245").
metabolite("C01246").
metabolite("C01250").
metabolite("C01251").
metabolite("C01260").
metabolite("C01261").
metabolite("C01268").
metabolite("C01269").
metabolite("C01277").
metabolite("C01279").
metabolite("C01300").
metabolite("C01302").
metabolite("C01304").
metabolite("C01326").
metabolite("C01328").
metabolite("C01330").
metabolite("C01346").
metabolite("C01352").
metabolite("C01419").
metabolite("C01429").
metabolite("C01530").
metabolite("C01598").
metabolite("C01635").
metabolite("C01636").
metabolite("C01637").
metabolite("C01638").
metabolite("C01640").
metabolite("C01642").
metabolite("C01643").
metabolite("C01644").
metabolite("C01645").
metabolite("C01646").
metabolite("C01647").
metabolite("C01648").
metabolite("C01649").
metabolite("C01650").
metabolite("C01651").
metabolite("C01652").
metabolite("C01653").
metabolite("C01684").
metabolite("C01694").
metabolite("C01722").
metabolite("C01724").
metabolite("C01755").
metabolite("C01762").
metabolite("C01801").
metabolite("C01811").
metabolite("C01883").
metabolite("C01885").
metabolite("C01909").
metabolite("C01931").
metabolite("C01953").
metabolite("C01967").
metabolite("C01997").
metabolite("C02038").
metabolite("C02047").
metabolite("C02051").
metabolite("C02073").
metabolite("C02100").
metabolite("C02163").
metabolite("C02165").
metabolite("C02191").
metabolite("C02218").
metabolite("C02220").
metabolite("C02222").
metabolite("C02229").
metabolite("C02282").
metabolite("C02291").
metabolite("C02407").
metabolite("C02412").
metabolite("C02430").
metabolite("C02472").
metabolite("C02504").
metabolite("C02530").
metabolite("C02550").
metabolite("C02553").
metabolite("C02554").
metabolite("C02567").
metabolite("C02593").
metabolite("C02637").
metabolite("C02667").
metabolite("C02693").
metabolite("C02700").
metabolite("C02702").
metabolite("C02714").
metabolite("C02737").
metabolite("C02739").
metabolite("C02794").
metabolite("C02843").
metabolite("C02938").
metabolite("C02972").
metabolite("C02984").
metabolite("C02987").
metabolite("C02988").
metabolite("C02992").
metabolite("C03021").
metabolite("C03023").
metabolite("C03024").
metabolite("C03028").
metabolite("C03082").
metabolite("C03090").
metabolite("C03127").
metabolite("C03161").
metabolite("C03175").
metabolite("C03205").
metabolite("C03226").
metabolite("C03232").
metabolite("C03294").
metabolite("C03360").
metabolite("C03373").
metabolite("C03384").
metabolite("C03402").
metabolite("C03406").
metabolite("C03451").
metabolite("C03475").
metabolite("C03479").
metabolite("C03492").
metabolite("C03496").
metabolite("C03506").
metabolite("C03511").
metabolite("C03512").
metabolite("C03518").
metabolite("C03541").
metabolite("C03638").
metabolite("C03722").
metabolite("C03723").
metabolite("C03734").
metabolite("C03794").
metabolite("C03812").
metabolite("C03824").
metabolite("C03838").
metabolite("C03849").
metabolite("C03881").
metabolite("C03883").
metabolite("C03892").
metabolite("C03895").
metabolite("C03912").
metabolite("C04076").
metabolite("C04088").
metabolite("C04090").
metabolite("C04133").
metabolite("C04144").
metabolite("C04145").
metabolite("C04232").
metabolite("C04233").
metabolite("C04236").
metabolite("C04246").
metabolite("C04252").
metabolite("C04256").
metabolite("C04294").
metabolite("C04295").
metabolite("C04302").
metabolite("C04308").
metabolite("C04312").
metabolite("C04327").
metabolite("C04332").
metabolite("C04352").
metabolite("C04376").
metabolite("C04411").
metabolite("C04425").
metabolite("C04431").
metabolite("C04432").
metabolite("C04441").
metabolite("C04454").
metabolite("C04489").
metabolite("C04494").
metabolite("C04500").
metabolite("C04506").
metabolite("C04517").
metabolite("C04549").
metabolite("C04556").
metabolite("C04618").
metabolite("C04619").
metabolite("C04620").
metabolite("C04633").
metabolite("C04637").
metabolite("C04640").
metabolite("C04677").
metabolite("C04681").
metabolite("C04682").
metabolite("C04688").
metabolite("C04691").
metabolite("C04692").
metabolite("C04727").
metabolite("C04728").
metabolite("C04732").
metabolite("C04733").
metabolite("C04734").
metabolite("C04735").
metabolite("C04736").
metabolite("C04748").
metabolite("C04752").
metabolite("C04763").
metabolite("C04801").
metabolite("C04807").
metabolite("C04823").
metabolite("C04827").
metabolite("C04874").
metabolite("C04895").
metabolite("C04896").
metabolite("C05102").
metabolite("C05108").
metabolite("C05125").
metabolite("C05138").
metabolite("C05139").
metabolite("C05140").
metabolite("C05200").
metabolite("C05223").
metabolite("C05309").
metabolite("C05313").
metabolite("C05330").
metabolite("C05335").
metabolite("C05336").
metabolite("C05345").
metabolite("C05378").
metabolite("C05379").
metabolite("C05397").
metabolite("C05399").
metabolite("C05400").
metabolite("C05401").
metabolite("C05402").
metabolite("C05437").
metabolite("C05440").
metabolite("C05485").
metabolite("C05487").
metabolite("C05488").
metabolite("C05489").
metabolite("C05512").
metabolite("C05533").
metabolite("C05535").
metabolite("C05643").
metabolite("C05688").
metabolite("C05699").
metabolite("C05701").
metabolite("C05702").
metabolite("C05729").
metabolite("C05744").
metabolite("C05745").
metabolite("C05746").
metabolite("C05747").
metabolite("C05748").
metabolite("C05749").
metabolite("C05750").
metabolite("C05751").
metabolite("C05752").
metabolite("C05753").
metabolite("C05754").
metabolite("C05755").
metabolite("C05756").
metabolite("C05757").
metabolite("C05758").
metabolite("C05759").
metabolite("C05760").
metabolite("C05761").
metabolite("C05762").
metabolite("C05763").
metabolite("C05764").
metabolite("C05778").
metabolite("C05824").
metabolite("C05863").
metabolite("C05864").
metabolite("C05872").
metabolite("C05873").
metabolite("C05874").
metabolite("C05925").
metabolite("C06010").
metabolite("C06015").
metabolite("C06054").
metabolite("C06055").
metabolite("C06113").
metabolite("C06156").
metabolite("C06253").
metabolite("C06604").
metabolite("C06606").
metabolite("C06814").
metabolite("C07090").
metabolite("C07091").
metabolite("C07281").
metabolite("C07282").
metabolite("C08817").
metabolite("C11355").
metabolite("C11482").
metabolite("C161ACP").
metabolite("C16A").
metabolite("C182ACP").
metabolite("C260COA").
metabolite("CER2").
metabolite("CER3").
metabolite("DB4P").
metabolite("DGPP").
metabolite("DMZYMST").
metabolite("DTP").
metabolite("EPST").
metabolite("ERTEOL").
metabolite("ERTROL").
metabolite("HBA").
metabolite("IGST").
metabolite("IIMZYMST").
metabolite("IIZYMST").
metabolite("IMZYMST").
metabolite("IPC").
metabolite("ISUCC").
metabolite("IZYMST").
metabolite("MACAC").
metabolite("MMET").
metabolite("MZYMST").
metabolite("N4HBZ").
metabolite("NAG").
metabolite("NMN").
metabolite("OIVAL").
metabolite("PHSP").
metabolite("PSPH").

orf("I00001").
orf("I00002").
orf("I00003").
orf("I00004").
orf("I00005").
orf("I00006").
orf("I00007").
orf("I00008").
orf("I00074").
orf("I00108").
orf("I00119").
orf("I00166").
orf("I00279").
orf("I00463").
orf("I00493").
orf("I00631").
orf("I01179").
orf("Q0045").
orf("Q0105").
orf("Q0250").
orf("Q0275").
orf("U100_").
orf("U101_").
orf("U102_").
orf("U103_").
orf("U104_").
orf("U105_").
orf("U107_").
orf("U108_").
orf("U109_").
orf("U10_").
orf("U110_").
orf("U111_").
orf("U112_").
orf("U114_").
orf("U115_").
orf("U116_").
orf("U117_").
orf("U119_").
orf("U120_").
orf("U121_").
orf("U122_").
orf("U125_").
orf("U128_").
orf("U12_").
orf("U130_").
orf("U134_").
orf("U136_").
orf("U138_").
orf("U139_").
orf("U13_").
orf("U141_").
orf("U142_").
orf("U143_").
orf("U144_").
orf("U145_").
orf("U146_").
orf("U147_").
orf("U14_").
orf("U150_").
orf("U152_").
orf("U153_").
orf("U154_").
orf("U155_").
orf("U161_").
orf("U162_").
orf("U163_").
orf("U164_").
orf("U165_").
orf("U166_").
orf("U167_").
orf("U16_").
orf("U171_").
orf("U174_").
orf("U175_").
orf("U176_").
orf("U179_").
orf("U17_").
orf("U181_").
orf("U184_").
orf("U185_").
orf("U186_").
orf("U187_").
orf("U18_").
orf("U190_").
orf("U191_").
orf("U192_").
orf("U193_").
orf("U195_").
orf("U197_").
orf("U19_").
orf("U1_").
orf("U200_").
orf("U201_").
orf("U205_").
orf("U207_").
orf("U20_").
orf("U213_").
orf("U214_").
orf("U218_").
orf("U219_").
orf("U21_").
orf("U220_").
orf("U222_").
orf("U223_").
orf("U227_").
orf("U228_").
orf("U229_").
orf("U22_").
orf("U24_").
orf("U26_").
orf("U27_").
orf("U28_").
orf("U29_").
orf("U2_").
orf("U30_").
orf("U32_").
orf("U33_").
orf("U34_").
orf("U35_").
orf("U36_").
orf("U37_").
orf("U39_").
orf("U3_").
orf("U40_").
orf("U41_").
orf("U42_").
orf("U43_").
orf("U44_").
orf("U46_").
orf("U47_").
orf("U48_").
orf("U4_").
orf("U50_").
orf("U51_").
orf("U53_").
orf("U55_").
orf("U56_").
orf("U57_").
orf("U58_").
orf("U5_").
orf("U62_").
orf("U64_").
orf("U65_").
orf("U66_").
orf("U68_").
orf("U69_").
orf("U6_").
orf("U70_").
orf("U72_").
orf("U73_").
orf("U74_").
orf("U75_").
orf("U76_").
orf("U78_").
orf("U79_").
orf("U7_").
orf("U81_").
orf("U82_").
orf("U83_").
orf("U84_").
orf("U85_").
orf("U86_").
orf("U88_").
orf("U89_").
orf("U8_").
orf("U90_").
orf("U93_").
orf("U94_").
orf("U96_").
orf("U99_").
orf("U9_").
orf("YAL023C").
orf("YAL062W").
orf("YAR073W").
orf("YAR075W").
orf("YBL013W").
orf("YBL030C").
orf("YBL035C").
orf("YBL042C").
orf("YBL045C").
orf("YBL056W").
orf("YBL067C").
orf("YBL068W").
orf("YBL076C").
orf("YBL098W").
orf("YBL099W").
orf("YBR001C").
orf("YBR002C").
orf("YBR003W").
orf("YBR006W").
orf("YBR011C").
orf("YBR018C").
orf("YBR019C").
orf("YBR020W").
orf("YBR023C").
orf("YBR029C").
orf("YBR034C").
orf("YBR035C").
orf("YBR038W").
orf("YBR046C").
orf("YBR058C").
orf("YBR068C").
orf("YBR069C").
orf("YBR084W").
orf("YBR085W").
orf("YBR092C").
orf("YBR093C").
orf("YBR111C").
orf("YBR115C").
orf("YBR117C").
orf("YBR121C").
orf("YBR125C").
orf("YBR126C").
orf("YBR149W").
orf("YBR153W").
orf("YBR154C").
orf("YBR166C").
orf("YBR184W").
orf("YBR196C").
orf("YBR218C").
orf("YBR221C").
orf("YBR243C").
orf("YBR244W").
orf("YBR249C").
orf("YBR252W").
orf("YBR256C").
orf("YBR263W").
orf("YBR278W").
orf("YBR291C").
orf("YBR294W").
orf("YBR298C").
orf("YBR299W").
orf("YCL009C").
orf("YCL018W").
orf("YCL025C").
orf("YCL030C").
orf("YCL040W").
orf("YCL043C").
orf("YCL050C").
orf("YCL064C").
orf("YCR005C").
orf("YCR012W").
orf("YCR014C").
orf("YCR028C").
orf("YCR036W").
orf("YCR048W").
orf("YCR053W").
orf("YCR073W-A").
orf("YDL006W").
orf("YDL021W").
orf("YDL022W").
orf("YDL024C").
orf("YDL033C").
orf("YDL045C").
orf("YDL047W").
orf("YDL052C").
orf("YDL055C").
orf("YDL066W").
orf("YDL067C").
orf("YDL080C").
orf("YDL085W").
orf("YDL086W").
orf("YDL090C").
orf("YDL093W").
orf("YDL095W").
orf("YDL100C").
orf("YDL102W").
orf("YDL103C").
orf("YDL122W").
orf("YDL131W").
orf("YDL134C").
orf("YDL140C").
orf("YDL141W").
orf("YDL150W").
orf("YDL164C").
orf("YDL171C").
orf("YDL182W").
orf("YDL188C").
orf("YDL210W").
orf("YDL215C").
orf("YDL232W").
orf("YDL236W").
orf("YDL238C").
orf("YDR001C").
orf("YDR007W").
orf("YDR009W").
orf("YDR019C").
orf("YDR023W").
orf("YDR035W").
orf("YDR037W").
orf("YDR044W").
orf("YDR045C").
orf("YDR046C").
orf("YDR047W").
orf("YDR050C").
orf("YDR058C").
orf("YDR069C").
orf("YDR074W").
orf("YDR075W").
orf("YDR111C").
orf("YDR121W").
orf("YDR127W").
orf("YDR147W").
orf("YDR148C").
orf("YDR156W").
orf("YDR158W").
orf("YDR208W").
orf("YDR226W").
orf("YDR232W").
orf("YDR236C").
orf("YDR242W").
orf("YDR268W").
orf("YDR272W").
orf("YDR294C").
orf("YDR297W").
orf("YDR300C").
orf("YDR321W").
orf("YDR341C").
orf("YDR353W").
orf("YDR354W").
orf("YDR380W").
orf("YDR399W").
orf("YDR400W").
orf("YDR402C").
orf("YDR404C").
orf("YDR408C").
orf("YDR410C").
orf("YDR419W").
orf("YDR436W").
orf("YDR454C").
orf("YDR481C").
orf("YDR497C").
orf("YDR502C").
orf("YDR503C").
orf("YDR508C").
orf("YDR529C").
orf("YDR530C").
orf("YDR531W").
orf("YDR536W").
orf("YDR538W").
orf("YEL002C").
orf("YEL011W").
orf("YEL021W").
orf("YEL024W").
orf("YEL041W").
orf("YEL046C").
orf("YEL047C").
orf("YEL055C").
orf("YEL058W").
orf("YEL063C").
orf("YER003C").
orf("YER005W").
orf("YER014W").
orf("YER042W").
orf("YER043C").
orf("YER052C").
orf("YER053C").
orf("YER056C").
orf("YER060W").
orf("YER060W-A").
orf("YER061C").
orf("YER062C").
orf("YER065C").
orf("YER069W").
orf("YER070W").
orf("YER073W").
orf("YER081W").
orf("YER087W").
orf("YER089C").
orf("YER090W").
orf("YER091C").
orf("YER098W").
orf("YER099C").
orf("YER133W").
orf("YER144C").
orf("YER151C").
orf("YER170W").
orf("YER178W").
orf("YER183C").
orf("YFL001W").
orf("YFL011W").
orf("YFL017C").
orf("YFL018C").
orf("YFL022C").
orf("YFL036W").
orf("YFL053W").
orf("YFL055W").
orf("YFR010W").
orf("YFR015C").
orf("YFR019W").
orf("YFR025C").
orf("YFR030W").
orf("YFR033C").
orf("YFR047C").
orf("YFR053C").
orf("YFR055W").
orf("YGL001C").
orf("YGL009C").
orf("YGL012W").
orf("YGL017W").
orf("YGL019W").
orf("YGL026C").
orf("YGL027C").
orf("YGL037C").
orf("YGL055W").
orf("YGL062W").
orf("YGL063W").
orf("YGL070C").
orf("YGL125W").
orf("YGL130W").
orf("YGL148W").
orf("YGL154C").
orf("YGL186C").
orf("YGL187C").
orf("YGL191W").
orf("YGL202W").
orf("YGL205W").
orf("YGL234W").
orf("YGL245W").
orf("YGL248W").
orf("YGL253W").
orf("YGR007W").
orf("YGR012W").
orf("YGR019W").
orf("YGR037C").
orf("YGR043C").
orf("YGR055W").
orf("YGR065C").
orf("YGR087C").
orf("YGR094W").
orf("YGR121C").
orf("YGR123C").
orf("YGR124W").
orf("YGR125W").
orf("YGR155W").
orf("YGR170W").
orf("YGR171C").
orf("YGR177C").
orf("YGR180C").
orf("YGR183C").
orf("YGR191W").
orf("YGR192C").
orf("YGR194C").
orf("YGR199W").
orf("YGR202C").
orf("YGR204W").
orf("YGR208W").
orf("YGR240C").
orf("YGR244C").
orf("YGR248W").
orf("YGR254W").
orf("YGR255C").
orf("YGR256W").
orf("YGR264C").
orf("YGR286C").
orf("YGR287C").
orf("YGR292W").
orf("YHL011C").
orf("YHL012W").
orf("YHL032C").
orf("YHL036W").
orf("YHR001W-A").
orf("YHR007C").
orf("YHR008C").
orf("YHR011W").
orf("YHR018C").
orf("YHR019C").
orf("YHR020W").
orf("YHR025W").
orf("YHR042W").
orf("YHR043C").
orf("YHR044C").
orf("YHR046C").
orf("YHR051W").
orf("YHR063C").
orf("YHR068W").
orf("YHR072W").
orf("YHR074W").
orf("YHR091C").
orf("YHR102W").
orf("YHR123W").
orf("YHR137W").
orf("YHR143W-A").
orf("YHR144C").
orf("YHR163W").
orf("YHR174W").
orf("YHR183W").
orf("YHR190W").
orf("YHR201C").
orf("YHR205W").
orf("YHR208W").
orf("YHR215W").
orf("YHR216W").
orf("YIL021W").
orf("YIL035C").
orf("YIL043C").
orf("YIL053W").
orf("YIL066C").
orf("YIL074C").
orf("YIL078W").
orf("YIL085C").
orf("YIL111W").
orf("YIL125W").
orf("YIL139C").
orf("YIL145C").
orf("YIL155C").
orf("YIL156W").
orf("YIL160C").
orf("YIL162W").
orf("YIL167W").
orf("YIL168W").
orf("YIL172C").
orf("YIR031C").
orf("YIR032C").
orf("YIR037W").
orf("YJL002C").
orf("YJL026W").
orf("YJL052W").
orf("YJL068C").
orf("YJL087C").
orf("YJL088W").
orf("YJL090C").
orf("YJL101C").
orf("YJL121C").
orf("YJL126W").
orf("YJL129C").
orf("YJL130C").
orf("YJL134W").
orf("YJL140W").
orf("YJL148W").
orf("YJL153C").
orf("YJL155C").
orf("YJL164C").
orf("YJL166W").
orf("YJL167W").
orf("YJL197W").
orf("YJL200C").
orf("YJL216C").
orf("YJL219W").
orf("YJL221C").
orf("YJR006W").
orf("YJR009C").
orf("YJR010W").
orf("YJR019C").
orf("YJR043C").
orf("YJR049C").
orf("YJR051W").
orf("YJR063W").
orf("YJR066W").
orf("YJR073C").
orf("YJR077C").
orf("YJR078W").
orf("YJR095W").
orf("YJR104C").
orf("YJR105W").
orf("YJR109C").
orf("YJR130C").
orf("YJR133W").
orf("YJR137C").
orf("YJR139C").
orf("YJR143C").
orf("YJR148W").
orf("YJR153W").
orf("YJR159W").
orf("YKL001C").
orf("YKL004W").
orf("YKL026C").
orf("YKL035W").
orf("YKL055C").
orf("YKL067W").
orf("YKL085W").
orf("YKL104C").
orf("YKL106W").
orf("YKL120W").
orf("YKL127W").
orf("YKL132C").
orf("YKL141W").
orf("YKL144C").
orf("YKL150W").
orf("YKL152C").
orf("YKL166C").
orf("YKL181W").
orf("YKL182W").
orf("YKL184W").
orf("YKL192C").
orf("YKL194C").
orf("YKL203C").
orf("YKL211C").
orf("YKL216W").
orf("YKL217W").
orf("YKR002W").
orf("YKR009C").
orf("YKR031C").
orf("YKR039W").
orf("YKR053C").
orf("YKR066C").
orf("YKR069W").
orf("YKR080W").
orf("YKR093W").
orf("YKR097W").
orf("YKR098C").
orf("YLL018C").
orf("YLL061W").
orf("YLL062C").
orf("YLR027C").
orf("YLR028C").
orf("YLR038C").
orf("YLR044C").
orf("YLR056W").
orf("YLR060W").
orf("YLR081W").
orf("YLR092W").
orf("YLR100C").
orf("YLR133W").
orf("YLR134W").
orf("YLR138W").
orf("YLR142W").
orf("YLR155C").
orf("YLR157C").
orf("YLR158C").
orf("YLR160C").
orf("YLR172C").
orf("YLR174W").
orf("YLR180W").
orf("YLR195C").
orf("YLR209C").
orf("YLR231C").
orf("YLR237W").
orf("YLR240W").
orf("YLR245C").
orf("YLR258W").
orf("YLR260W").
orf("YLR286C").
orf("YLR299W").
orf("YLR303W").
orf("YLR304C").
orf("YLR307W").
orf("YLR308W").
orf("YLR328W").
orf("YLR348C").
orf("YLR354C").
orf("YLR355C").
orf("YLR359W").
orf("YLR377C").
orf("YLR382C").
orf("YLR395C").
orf("YLR420W").
orf("YLR432W").
orf("YLR433C").
orf("YLR438W").
orf("YLR450W").
orf("YML008C").
orf("YML016C").
orf("YML019W").
orf("YML035C").
orf("YML054C").
orf("YML056C").
orf("YML057W").
orf("YML070W").
orf("YML075C").
orf("YML082W").
orf("YML100W").
orf("YML120C").
orf("YML123C").
orf("YML126C").
orf("YMR006C").
orf("YMR008C").
orf("YMR013C").
orf("YMR015C").
orf("YMR056C").
orf("YMR062C").
orf("YMR083W").
orf("YMR101C").
orf("YMR105C").
orf("YMR108W").
orf("YMR113W").
orf("YMR120C").
orf("YMR145C").
orf("YMR149W").
orf("YMR180C").
orf("YMR189W").
orf("YMR202W").
orf("YMR205C").
orf("YMR208W").
orf("YMR217W").
orf("YMR220W").
orf("YMR223W").
orf("YMR250W").
orf("YMR256C").
orf("YMR261C").
orf("YMR272C").
orf("YMR300C").
orf("YMR304W").
orf("YMR323W").
orf("YNL009W").
orf("YNL029C").
orf("YNL045W").
orf("YNL052W").
orf("YNL071W").
orf("YNL073W").
orf("YNL102W").
orf("YNL113W").
orf("YNL117W").
orf("YNL130C").
orf("YNL141W").
orf("YNL142W").
orf("YNL151C").
orf("YNL186W").
orf("YNL192W").
orf("YNL241C").
orf("YNL248C").
orf("YNL256W").
orf("YNL262W").
orf("YNL270C").
orf("YNL277W").
orf("YNL280C").
orf("YNL292W").
orf("YNL299W").
orf("YNL316C").
orf("YNL318C").
orf("YNR001C").
orf("YNR003C").
orf("YNR012W").
orf("YNR016C").
orf("YNR019W").
orf("YNR032W").
orf("YNR033W").
orf("YNR034W").
orf("YNR041C").
orf("YNR043W").
orf("YNR057C").
orf("YNR058W").
orf("YOL005C").
orf("YOL010W").
orf("YOL011W").
orf("YOL020W").
orf("YOL033W").
orf("YOL052C").
orf("YOL055C").
orf("YOL056W").
orf("YOL058W").
orf("YOL059W").
orf("YOL061W").
orf("YOL064C").
orf("YOL096C").
orf("YOL097C").
orf("YOL103W").
orf("YOL115W").
orf("YOL140W").
orf("YOL143C").
orf("YOL156W").
orf("YOR005C").
orf("YOR011W").
orf("YOR061W").
orf("YOR065W").
orf("YOR071C").
orf("YOR085W").
orf("YOR095C").
orf("YOR103C").
orf("YOR116C").
orf("YOR124C").
orf("YOR130C").
orf("YOR136W").
orf("YOR143C").
orf("YOR151C").
orf("YOR168W").
orf("YOR171C").
orf("YOR184W").
orf("YOR192C").
orf("YOR207C").
orf("YOR209C").
orf("YOR210W").
orf("YOR221C").
orf("YOR224C").
orf("YOR236W").
orf("YOR241W").
orf("YOR251C").
orf("YOR274W").
orf("YOR278W").
orf("YOR303W").
orf("YOR321W").
orf("YOR323C").
orf("YOR330C").
orf("YOR335C").
orf("YOR340C").
orf("YOR341W").
orf("YOR348C").
orf("YOR360C").
orf("YOR374W").
orf("YOR375C").
orf("YOR377W").
orf("YOR388C").
orf("YOR393W").
orf("YPL001W").
orf("YPL017C").
orf("YPL023C").
orf("YPL040C").
orf("YPL072W").
orf("YPL091W").
orf("YPL104W").
orf("YPL111W").
orf("YPL117C").
orf("YPL148C").
orf("YPL160W").
orf("YPL167C").
orf("YPL172C").
orf("YPL179W").
orf("YPL188W").
orf("YPL203W").
orf("YPL212C").
orf("YPL214C").
orf("YPL227C").
orf("YPL228W").
orf("YPL231W").
orf("YPL258C").
orf("YPL262W").
orf("YPL265W").
orf("YPL266W").
orf("YPL268W").
orf("YPL273W").
orf("YPL275W").
orf("YPL276W").
orf("YPL281C").
orf("YPR001W").
orf("YPR006C").
orf("YPR010C").
orf("YPR026W").
orf("YPR033C").
orf("YPR035W").
orf("YPR047W").
orf("YPR060C").
orf("YPR069C").
orf("YPR073C").
orf("YPR074C").
orf("YPR081C").
orf("YPR110C").
orf("YPR121W").
orf("YPR138C").
orf("YPR145W").
orf("YPR160W").
orf("YPR167C").
orf("YPR175W").
orf("YPR176C").
orf("YPR187W").
orf("YPR190C").
orf("YPR191W").

compartment(cytosol).
compartment(medium).
compartment(mitochondrion).

day(1).


