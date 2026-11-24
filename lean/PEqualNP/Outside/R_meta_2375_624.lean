import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The five independent sets of size four and ten maximal sets of size three index fifteen rows.
-- Assign each row to one of its two false terminal wires. Vertex symmetries and exchanging the two
-- wires identify 272 colorings of these rows. In a table word the high part is the triangle code.
-- Low bit s permits the corresponding coloring of the five star rows.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 7000000 in
theorem PEqualNP.Outside.R_meta_2375_624
    (small : ∀ (C : Circuit) (a b tag : ℕ) (s : Fin 32),
      let w := PEqualNP.CleanedNonEdge.wireVal 10 C
      let f := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
        (fun t => x (Fin.ofNat 10 (t / 10)) && x (Fin.ofNat 10 (t % 10)))
      let row := fun (j : Fin 15) (i : Fin 10) => ([116,201,402,554,773,50,69,104,138,208,276,385,521,548,770] : List ℕ).getD j.val 0 |>.testBit i.val
      let full := if (4276676736 : ℕ).testBit s.val then a else b
      FanInTwo C → C.size ≤ 18 → tag ∈ ([2147516555,6451667119,16106189007,23803693775] : List ℕ) → tag.testBit s.val = true →
      (∀ j : Fin 15, (if (tag / 4294967296 * 32 + s.val).testBit j.val then w a (row j) else w b (row j)) = false) →
      (∃ x, w a x = true ∧ w b x = false) → (∃ x, w a x = false ∧ w b x = true) →
      (∀ i : Fin 10, ∃ j : Fin 15, j.val < 5 ∧ w full (row j) ≠ w full (fun k : Fin 10 => (k == i) || row j k)) →
      ¬ (∀ x, (w a x && w b x) = f x))
    (middle : ∀ (C : Circuit) (a b tag : ℕ) (s : Fin 32),
      let w := PEqualNP.CleanedNonEdge.wireVal 10 C
      let f := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
        (fun t => x (Fin.ofNat 10 (t / 10)) && x (Fin.ofNat 10 (t % 10)))
      let row := fun (j : Fin 15) (i : Fin 10) => ([116,201,402,554,773,50,69,104,138,208,276,385,521,548,770] : List ℕ).getD j.val 0 |>.testBit i.val
      let full := if (4276676736 : ℕ).testBit s.val then a else b
      FanInTwo C → C.size ≤ 18 → tag ∈ ([33301789951,50209730747,58175753099,97442115771] : List ℕ) → tag.testBit s.val = true →
      (∀ j : Fin 15, (if (tag / 4294967296 * 32 + s.val).testBit j.val then w a (row j) else w b (row j)) = false) →
      (∃ x, w a x = true ∧ w b x = false) → (∃ x, w a x = false ∧ w b x = true) →
      (∀ i : Fin 10, ∃ j : Fin 15, j.val < 5 ∧ w full (row j) ≠ w full (fun k : Fin 10 => (k == i) || row j k)) →
      ¬ (∀ x, (w a x && w b x) = f x))
    (large : ∀ (C : Circuit) (a b tag : ℕ) (s : Fin 32),
      let w := PEqualNP.CleanedNonEdge.wireVal 10 C
      let f := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
        (fun t => x (Fin.ofNat 10 (t / 10)) && x (Fin.ofNat 10 (t % 10)))
      let row := fun (j : Fin 15) (i : Fin 10) => ([116,201,402,554,773,50,69,104,138,208,276,385,521,548,770] : List ℕ).getD j.val 0 |>.testBit i.val
      let full := if (4276676736 : ℕ).testBit s.val then a else b
      FanInTwo C → C.size ≤ 18 → tag ∈ ([67574152123,102827553023,126710677643,136109076667,170725002447,187619671983,205349965775,253419851567,479073438603,734439407659] : List ℕ) → tag.testBit s.val = true →
      (∀ j : Fin 15, (if (tag / 4294967296 * 32 + s.val).testBit j.val then w a (row j) else w b (row j)) = false) →
      (∃ x, w a x = true ∧ w b x = false) → (∃ x, w a x = false ∧ w b x = true) →
      (∀ i : Fin 10, ∃ j : Fin 15, j.val < 5 ∧ w full (row j) ≠ w full (fun k : Fin 10 => (k == i) || row j k)) →
      ¬ (∀ x, (w a x && w b x) = f x)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true := by
  classical
  have colorOrbits : ∀ color : (Fin 10 → Bool) → Bool,
      let f := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
        (fun t => x (Fin.ofNat 10 (t / 10)) && x (Fin.ofNat 10 (t % 10)))
      let row := fun (j : Fin 15) (i : Fin 10) => ([116,201,402,554,773,50,69,104,138,208,276,385,521,548,770] : List ℕ).getD j.val 0 |>.testBit i.val
      ∃ (p : Equiv.Perm (Fin 10)) (flip : Bool) (tag : ℕ) (s : Fin 32),
        (tag ∈ ([2147516555,6451667119,16106189007,23803693775] : List ℕ) ∨ tag ∈ ([33301789951,50209730747,58175753099,97442115771] : List ℕ) ∨ tag ∈ ([67574152123,102827553023,126710677643,136109076667,170725002447,187619671983,205349965775,253419851567,479073438603,734439407659] : List ℕ)) ∧
        tag.testBit s.val = true ∧
        (∀ x, f (x ∘ p) = f x) ∧
        (∀ j : Fin 15, color (row j ∘ p) = if flip then !((tag / 4294967296 * 32 + s.val).testBit j.val) else (tag / 4294967296 * 32 + s.val).testBit j.val) := by
    let vWords : List (List ℕ) :=
      [[654820258320,624752330115,589321040400,554959176855,107479201155,103185265815,620427088440,633308873985,38996898360,13222905495,247034180865,208378402455,550649598585,580712305665,34718626425,30419490435,517902316545,483540473475,81642554745,98823476280,212640990585,238409782800,487787398200,496375268880,654013059090,623945130885,589860913170,555493828500,108019073925,103719917460,628259950680,641141736225],
       [176486039640,159299896980,384523322145,354455393940,559745994825,568328623905,172124229705,154938087045,311710209825,285941438085,90738950985,86439794520,350046593865,362928379410,281595291480,298776233490,620154542130,633046769925,40071424050,14302652310,245425004805,206764005270,628794603600,641686831395,177020692560,159844992150,382374273315,352306345110,9956505705,27137447715,138265712745,164039726085],
       [414754297635,423347368965,228311957865,232600672080,356621164905,369502950450,427756169040,436349240370,551451576690,581524726020,35520604530,31231910790,516020592900,481658749830,560008100160,568606392615,173733407040,156557706630,309293834535,283519841670,9683958120,26870121255,139340237160,165114250500,414486971175,423074821380,498907545960,507495416640,305099121000,300799985010,444685427520,431798420850],
       [83256953205,100437874740,211561245045,237340479510,486707652660,495305965590,91813476675,87519541335,349774047555,362666275350,279980894295,297167057430,228841388385,233145765975,358497667425,371389895220,425607118935,434194969140,499709524065,508307836995,305901099105,301612405365,442803703875,429916697205]]

    let qWords : List (List ℕ) :=
      [[1070935975390360080,1070877713912513040,1057164455350379280,1033801976470774800,1057085306946339600,1033781089544582160,927379338753749280,927327675849326880,841828400633225520,603138665401753920,841761349613797680,603123277286748480,895069915767378720,898729446861902880,823290497686835760,611616173856068160,835675963460293680,620342108535001920,894957791608914720,898668985607861280,823183872339558960,611567809986638400,835636389132444720,620309132780577600,1066697345183527425,1066606106944684545,1061403059793699585,1046484838803252225,1061257957867668225,1046430975116063745,931518995738407170,931533286355976450],
       [858617947483283715,641055315297771780,858666315127341315,641089392324260100,916164042052342530,902935057368552450,848557279187046915,632578354451780100,831387842348454915,628637902296978180,916051917893878530,902808642592519170,848533095742259715,632645409245835780,831315291259610115,628670880064545540,994915728915443745,994828889725550625,774291986312339505,400494270312816705,774154582721970225,400443705912340545,1003294016106934290,1003306107200028690,786842928719077395,425728057876357140,786886897314185235,425759935378370580,485502929438249010,544044567143583810,489675584653496355,560801137232646180],
       [687825710109298755,700409624983113780,485396304090972210,543925850703212610,489651401208709155,560863792977752100,687757558069403715,700440403226206260,966845128607269665,969941580932908065,751515671393993265,395728229661606465,762774979629679665,403891085571654465,983700650448913170,961464329107080210,781021083101037075,420962017225146900,745836972946359315,408014228412302100,481264517466292530,530801018038059330,493914407331692835,564512057427427620,674054258520359235,695115408044327220,475072505965511730,546845327879111490,466611751108019235,534112948878115620,681935712451363395,677664088307860020],
       [966681340537750305,969864632053281825,751355182611186225,395658979117642305,762751894437241905,403872399428166465,983602815901385490,961354403466458130,780976012981715475,420975208583672340,745747934231929875,407995542268814100,481174381254426930,530696591208624450,493873736261320995,564523049261478180,673965219805929795,695092322851889460,475088995100922930,546859617490047810,466595263482434595,534061284967060260,681914825776828995,677610224872329780]]

    let inverses : List (List ℕ) :=
      [[0,1,2,4,3,5,6,7,12,18,13,19,8,10,14,20,16,22,9,11,15,21,17,23,24,25,26,28,27,29,48,49],
       [72,96,73,97,50,52,74,98,76,100,51,53,75,99,77,101,30,31,36,42,37,43,54,55,78,102,79,103,60,66,84,108],
       [90,114,61,67,85,109,91,115,32,34,38,44,40,46,56,58,80,104,82,106,62,68,86,110,92,116,64,70,88,112,94,118],
       [33,35,39,45,41,47,57,59,81,105,83,107,63,69,87,111,93,117,65,71,89,113,95,119]]

    let firstTable : List (List ℕ) :=
      [[0,1,253,2,217,3,579,4,865,1083,866,5,867,6,868,7,289,75,471,76,435,2598,8,9,939,78,940,79,438,10,873,11],
       [37,795,39,256,38,220,40,12,1082,1084,1769,13,221,223,229,14,111,224,2634,261,112,225,45,4061,1300,1089,2635,15,439,227,231,4095],
       [901,1118,903,257,902,1733,904,265,3603,1948,1768,877,1732,1735,876,878,975,1336,474,475,976,2599,909,267,1736,1953,1773,879,1737,1739,2549,2583],
       [1119,1120,42,259,41,49,43,50,1984,1092,1771,1130,913,1094,914,16,114,1125,46,263,115,51,47,4059,1989,2333,1775,2331,915,2367,2547,2330],
       [1009,1226,1011,365,1047,1444,582,583,3495,2020,1876,949,1808,2025,1881,951,1010,1805,1012,373,1048,2671,1017,375,1804,1807,948,950,1809,1811,2441,2511],
       [1262,2525,1480,589,401,625,619,590,3929,3397,2641,17,502,1436,1580,1435,1841,2770,2707,3848,409,3884,411,4057,2713,3020,2642,3019,1652,1434,2437,2506],
       [3459,3893,1844,466,1912,2605,1917,1544,4110,4111,3573,680,3537,717,677,673,1840,2677,1845,1616,984,2606,2405,2401,3465,825,749,745,785,1647,676,672],
       [2056,3433,2061,1400,985,53,987,1399,4147,4118,681,679,716,715,709,671,1843,2984,1847,1398,986,2983,2475,2470,861,3193,1611,1606,781,1642,708,1605],
       [145,687,147,364,183,296,2742,369,1154,1156,1877,85,1372,1161,2743,87,146,292,148,84,184,297,153,3953,293,295,301,86,511,299,303,4023],
       [651,3246,332,765,400,729,405,3485,2381,3247,2626,3488,445,447,3704,3481,328,657,333,3557,120,3593,3917,3484,517,519,3776,3553,446,3807,3913,3480],
       [1190,2417,1408,481,1913,2662,2779,3740,4037,3289,2749,89,2785,2948,2750,2947,329,553,547,482,337,3812,339,3949,610,1508,1688,1507,1724,1506,2545,2578],
       [1192,3283,1197,483,121,3524,123,3517,3253,3254,2912,3127,125,3163,2911,3479,331,555,335,3771,122,3589,3987,3516,1472,2329,1470,2326,1471,2362,2542,3765],
       [1227,1228,150,367,186,1233,154,371,2092,1164,1879,1238,2097,2225,1883,2223,149,157,151,158,187,159,155,3951,1021,1166,1022,88,1023,2295,2439,2222],
       [1264,3391,1269,591,403,627,407,3699,3325,3326,2840,3055,1364,2221,1362,2218,193,3632,195,3625,194,3661,3915,3624,197,3235,2839,3551,1363,2290,2434,3693],
       [2128,3361,2133,1328,1915,2876,1919,1326,4255,4190,753,751,789,3085,1539,1534,1057,161,1059,1327,1058,2875,2403,2398,824,823,817,743,853,1714,816,1533],
       [1200,3362,2189,2185,1274,3091,2187,2182,4226,3256,3049,2183,787,2219,1570,1532,1202,3199,2259,2254,124,3587,2186,3729,859,2327,1678,1604,779,1640,1569,1531],
       [1513,1551,1622,761,1586,1660,2309,841,3711,2168,3569,142,2236,2241,3181,1220,1514,1552,2201,769,2165,3031,3274,4244,2164,2169,3073,1292,2167,2171,3380,1218],
       [1515,798,1696,835,725,799,805,806,2380,2385,2857,1076,1309,1077,179,1075,1516,1521,3067,771,733,735,4208,4273,1308,1937,2858,1933,1310,2151,3379,2146],
       [3675,2416,2272,1345,3533,2821,3217,215,3606,3897,3643,212,3607,213,3614,211,2200,1344,2203,1346,3037,2822,3344,3343,3681,425,645,421,609,1287,3409,1282],
       [2204,2421,2277,1041,106,1040,1184,1039,3933,173,177,205,176,169,175,167,2205,1901,2207,2115,1256,1897,1182,2110,389,172,1251,204,385,168,1246,1245],
       [3747,2524,2344,1453,2308,1452,2311,1454,3498,3969,3571,140,3753,353,573,349,3461,2893,3145,143,3109,2894,3272,3271,3499,141,3506,139,501,1215,3301,1210],
       [2560,2527,1488,1706,1489,1670,1490,592,3931,357,3794,355,500,565,571,347,2929,2768,2930,2803,107,2767,3307,4055,3722,2797,2644,1931,499,1426,2435,1208],
       [3462,3895,3789,464,3535,3758,537,535,3466,3899,3575,138,3539,351,675,346,3463,3686,465,463,3470,2608,3265,2399,3467,423,747,418,783,350,3264,669],
       [4005,321,317,529,104,319,313,311,3935,171,315,202,102,166,310,164,105,2761,1179,1390,103,1895,1174,1172,387,2760,314,201,382,165,705,163],
       [1587,690,1624,763,1588,1593,3175,843,2452,2457,2965,1004,1380,1865,2966,1861,653,691,697,698,661,663,4136,4165,1381,1005,71,1003,1382,2079,3451,2074],
       [654,658,1629,767,727,731,807,3483,2383,2387,2624,1002,1598,1863,2695,1858,655,659,699,3555,662,3591,4129,4128,1526,1935,2623,1930,448,1862,3911,3477],
       [2488,2419,1416,1634,3001,2660,3002,2731,4039,429,3866,427,3830,2725,2752,1859,1417,1562,1418,484,35,2659,3415,3947,608,637,643,419,607,1498,2543,1280],
       [2493,2423,1829,1827,968,966,1825,1822,393,1035,2689,1066,391,1030,1823,1028,969,1899,2043,1826,967,1894,2038,3513,601,600,1462,1065,383,1029,1244,1027],
       [2312,2529,2349,933,2313,1793,2315,2007,4041,65,69,133,281,64,1143,132,34,932,1112,931,1148,1789,1110,2002,68,61,67,59,277,60,1138,1137],
       [2565,2531,1757,1755,897,1791,1971,1754,285,927,2617,994,493,492,1354,993,896,894,1753,1750,895,1786,1966,3621,283,922,1751,920,275,921,1136,919],
       [4077,249,245,457,33,2653,1107,1318,4043,63,243,130,279,2652,242,129,32,247,241,239,31,1787,1102,1100,30,58,238,56,274,57,813,55],
       [29,891,28,456,97,958,96,957,27,26,2616,453,94,489,93,307,25,886,24,885,23,884,1101,883,22,597,21,235,20,271,19,18]]

    let secondTable : List (List ℕ) :=
      [[0,1,1537,3,1921,387,3075,7,2049,515,3203,135,3843,775,4615,15,2113,579,3267,199,3907,839,4679,79,4099,1031,4871,271,5767,1167,6159,31],
       [0,1,2,3,3457,5,3459,7,3585,133,3587,135,4997,13,4999,15,1346,1347,18,19,4291,1351,3475,23,4483,1479,3603,151,5831,1359,5015,31],
       [0,1,2,3,450,451,6,7,642,643,134,135,12,13,14,15,1346,1347,460,461,838,839,462,463,1030,1031,654,655,1358,1359,30,31],
       [0,1,2,3,386,387,6,7,5121,9,5123,11,5507,395,5127,15,16,17,18,19,402,403,22,23,5137,25,5139,27,5523,411,5143,31],
       [0,1,2,3,4,5,6,7,1026,1027,10,11,12,13,14,15,1028,1029,1036,1037,20,21,22,23,1030,1031,1038,1039,1046,1047,30,31],
       [0,1,1537,3,4,5,1541,7,132,133,1669,135,12,13,1549,15,16,17,1553,19,20,21,1557,23,148,149,1685,151,28,29,1565,31],
       [0,1,1537,3,1921,387,3075,7,8,9,1545,11,1929,395,3083,15,16,17,1553,19,1937,403,3091,23,24,25,1561,27,1945,411,3099,31],
       [0,1,1537,3,4,5,1541,7,8,9,1545,11,12,13,1549,15,16,17,1553,19,20,21,1557,23,24,25,1561,27,28,29,1565,31],
       [0,1,1537,3,4,5,1541,7,132,133,1669,135,12,13,1549,15,196,197,1733,199,76,77,1613,79,268,269,1805,271,28,29,1565,31],
       [0,1,2,3,4,5,6,7,132,133,134,135,12,13,14,15,16,17,18,19,20,21,22,23,148,149,150,151,28,29,30,31],
       [0,1,1537,3,1921,387,3075,7,2049,515,3203,135,3843,775,4615,15,16,17,1553,19,1937,403,3091,23,2065,531,3219,151,3859,791,4631,31],
       [0,1,1537,3,4,5,1541,7,132,133,1669,135,12,13,1549,15,16,17,1553,19,20,21,1557,23,148,149,1685,151,28,29,1565,31],
       [0,1,2,3,386,387,6,7,1026,1027,10,11,394,395,14,15,1090,1091,74,75,458,459,78,79,1030,1031,1038,1039,1422,1423,30,31],
       [0,1,2,3,3521,5,3523,7,8,9,10,11,12,13,14,15,3528,3532,3530,3534,3529,3533,3531,3535,24,25,26,27,3545,29,3547,31],
       [0,1,2,3,386,387,6,7,8,9,10,11,394,395,14,15,16,17,18,19,402,403,22,23,24,25,26,27,410,411,30,31],
       [0,1,2,3,3521,5,3523,5349,8,9,10,11,5355,5347,5353,5345,3528,6827,3530,6825,3529,6819,3531,6817,24,6826,5368,6824,5354,5346,5352,5344],
       [0,1,1537,3,1921,387,3075,7,8,9,1545,11,1929,395,3083,15,72,73,1609,75,1993,459,3147,79,24,25,1561,27,1945,411,3099,31],
       [0,1,1665,3,3521,5,3523,5349,2177,1027,1669,2533,6021,3427,611,2529,4545,1029,4677,4003,7107,6307,1189,4001,4547,5413,1187,2785,613,3425,609,608]]

    let words : List (List ℕ) :=
      [[2147516555,6451667119,16106189007,23803693775,33301789951,50209730747,58175753099,67574152123,97442115771,102827553023,126710677643,136109076667,170725002447,187619671983,205349965775,253419851567,479073438603,734439407659]]


    let lookup (table : List (List ℕ)) (i : ℕ) : ℕ := ((table.getD (i / 32) []).getD (i % 32) 0)
    let vertex (k : Fin 120) (i : Fin 10) : Fin 10 := Fin.ofNat 10 ((lookup vWords k.val >>> (4*i.val)) % 16)
    let moveRow (k : Fin 120) (j : Fin 15) : Fin 15 := Fin.ofNat 15 ((lookup qWords k.val >>> (4*j.val)) % 16)
    let inv (k : Fin 120) : Fin 120 := Fin.ofNat 120 (lookup inverses k.val)
    let row := fun (j : Fin 15) (i : Fin 10) => ([116,201,402,554,773,50,69,104,138,208,276,385,521,548,770] : List ℕ).getD j.val 0 |>.testBit i.val
    let endpoints : List ℕ := [1,12,23,34,40,5,16,27,38,49,57,79,96,68,85]
    let lft (t : ℕ) := Fin.ofNat 10 (t / 10)
    let rgt (t : ℕ) := Fin.ofNat 10 (t % 10)
    let edge (x : Fin 10 → Bool) := endpoints.any (fun t => x (lft t) && x (rgt t))
    let adj (i j : Fin 10) := endpoints.any (fun t => ((i == lft t) && (j == rgt t)) || ((j == lft t) && (i == rgt t)))
    have inverseLeft : ∀ k i, vertex (inv k) (vertex k i) = i := by decide +kernel
    have inverseRight : ∀ k i, vertex k (vertex (inv k) i) = i := by decide +kernel
    let perm (k : Fin 120) : Equiv.Perm (Fin 10) :=
      ⟨vertex k,vertex (inv k),inverseLeft k,inverseRight k⟩
    have adj_perm : ∀ k i j, adj (vertex k i) (vertex k j) = adj i j := by decide +kernel
    have row_bits : ∀ k j i, row j (vertex k i) = row (moveRow k j) i := by decide +kernel
    have row_move (k : Fin 120) (j : Fin 15) : row j ∘ perm k = row (moveRow k j) :=
      funext (row_bits k j)
    have edge_iff (x : Fin 10 → Bool) : edge x = true ↔ ∃ i j, adj i j = true ∧ x i = true ∧ x j = true := by
      simp only [edge,adj,List.any_eq_true,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq]
      constructor
      · rintro ⟨t,ht,hl,hr⟩
        exact ⟨lft t,rgt t,⟨t,ht,Or.inl ⟨rfl,rfl⟩⟩,hl,hr⟩
      · rintro ⟨i,j,⟨t,ht,h|h⟩,hi,hj⟩
        · exact ⟨t,ht,h.1 ▸ hi,h.2 ▸ hj⟩
        · exact ⟨t,ht,h.1 ▸ hj,h.2 ▸ hi⟩
    have edge_move (k : Fin 120) (x : Fin 10 → Bool) : edge (x ∘ perm k) = edge x := by
      apply Bool.eq_iff_iff.mpr
      rw [edge_iff,edge_iff]
      constructor
      · rintro ⟨i,j,h,hi,hj⟩
        exact ⟨vertex k i,vertex k j,(adj_perm k i j).trans h,hi,hj⟩
      · rintro ⟨i,j,h,hi,hj⟩
        refine ⟨vertex (inv k) i,vertex (inv k) j,(adj_perm (inv k) i j).trans h,?_,?_⟩
        · change x (vertex k (vertex (inv k) i)) = true; simpa only [inverseRight] using hi
        · change x (vertex k (vertex (inv k) j)) = true; simpa only [inverseRight] using hj

    let star (i : Fin 5) : Fin 15 := ⟨i,by omega⟩
    let tri (i : Fin 10) : Fin 15 := ⟨5+i,by omega⟩
    let si (k : Fin 120) (i : Fin 5) := Fin.ofNat 5 (moveRow k (star i)).val
    let ti (k : Fin 120) (i : Fin 10) := Fin.ofNat 10 ((moveRow k (tri i)).val-5)
    have star_row : ∀ k i, moveRow k (star i) = star (si k i) := by decide +kernel
    have tri_row : ∀ k i, moveRow k (tri i) = tri (ti k i) := by decide +kernel
    let word (t : Fin 18) := lookup words t.val
    let phase (e x : Bool) := if e then !x else x
    let A (z : Fin 1024) := Fin.ofNat 120 (lookup firstTable z.val / 18 / 2)
    let af (z : Fin 1024) := (lookup firstTable z.val / 18).testBit 0
    let idA (z : Fin 1024) := Fin.ofNat 18 (lookup firstTable z.val)
    let second (t : Fin 18) (l : Fin 32) := lookup secondTable (32*t.val+l.val)
    let B (t : Fin 18) (l : Fin 32) := Fin.ofNat 120 (second t l / 32 / 2)
    let bf (t : Fin 18) (l : Fin 32) := (second t l / 32).testBit 0
    let sid (t : Fin 18) (l : Fin 32) := Fin.ofNat 32 (second t l)
    have first_tri : ∀ (z : Fin 1024) j, z.val.testBit (ti (A z) j).val =
        phase (af z) ((word (idA z) / 4294967296).testBit j.val) := by decide +kernel
    have second_tri : ∀ t l j, (word t / 4294967296).testBit (ti (B t l) j).val =
        phase (bf t l) ((word t / 4294967296).testBit j.val) := by decide +kernel
    have second_star : ∀ t l j, l.val.testBit (si (B t l) j).val =
        phase (bf t l) ((sid t l).val.testBit j.val) := by decide +kernel
    have allowed : ∀ t l, (word t).testBit (sid t l).val = true := by decide +kernel
    have listed : ∀ t, word t ∈ ([2147516555,6451667119,16106189007,23803693775] : List ℕ) ∨ word t ∈ ([33301789951,50209730747,58175753099,97442115771] : List ℕ) ∨ word t ∈ ([67574152123,102827553023,126710677643,136109076667,170725002447,187619671983,205349965775,253419851567,479073438603,734439407659] : List ℕ) := by decide +kernel
    have low : ∀ (t : Fin 18) (s : Fin 32) (j : Fin 5),
        (word t / 4294967296 * 32 + s.val).testBit (star j).val = s.val.testBit j.val := by decide +kernel
    have high : ∀ (t : Fin 18) (s : Fin 32) (j : Fin 10),
        (word t / 4294967296 * 32 + s.val).testBit (tri j).val = (word t / 4294967296).testBit j.val := by decide +kernel

    let pack {n : ℕ} (bits : Fin n → Bool) : Fin (2^n) :=
      ⟨(BitVec.ofBoolListLE (List.ofFn bits)).toNat,by
        simpa only [List.length_ofFn] using (BitVec.ofBoolListLE (List.ofFn bits)).isLt⟩
    have pack_bit {n : ℕ} (bits : Fin n → Bool) (i : Fin n) : (pack bits).val.testBit i.val = bits i := by
      change (BitVec.ofBoolListLE (List.ofFn bits)).toNat.testBit i.val = bits i
      rw [BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem _ _ (by simpa using i.isLt),List.getElem_ofFn]
    have phase_twice (e x : Bool) : phase e (phase e x) = x := by cases e <;> cases x <;> rfl
    have phase_comp (a b x : Bool) : phase a (phase b x) = phase (xor a b) x := by cases a <;> cases b <;> cases x <;> rfl
    intro color f initialRow
    let z : Fin 1024 := pack (fun i : Fin 10 => color (row (tri i)))
    let t := idA z
    let u := A z
    let e := af z
    let l : Fin 32 := pack (fun i : Fin 5 => phase e (color (row (star i) ∘ perm u)))
    let k := B t l
    let d := bf t l
    let s := sid t l
    have aStar (i : Fin 5) : color (row (star i) ∘ perm u) = phase e (l.val.testBit i.val) := by
      rw [show l.val.testBit i.val = phase e (color (row (star i) ∘ perm u)) from pack_bit _ _,phase_twice]
    have aTri (i : Fin 10) : color (row (tri i) ∘ perm u) = phase e ((word t / 4294967296).testBit i.val) := by
      rw [row_move,tri_row, ← pack_bit (fun j : Fin 10 => color (row (tri j))) (ti u i)]
      exact first_tri z i
    refine ⟨(perm u).trans (perm k),xor e d,word t,s,listed t,allowed t l,?_,?_⟩
    · intro x
      change edge ((x ∘ perm k) ∘ perm u) = edge x
      rw [edge_move,edge_move]
    · intro j
      change color ((row j ∘ perm k) ∘ perm u) = phase (xor e d) ((word t / 4294967296 * 32+s.val).testBit j.val)
      by_cases h : j.val < 5
      · let i : Fin 5 := ⟨j.val,h⟩
        have idj : j = star i := Fin.ext rfl
        rw [idj,row_move,star_row,aStar,show l.val.testBit (si k i).val = phase d (s.val.testBit i.val) from second_star t l i,low,phase_comp]
      · let i : Fin 10 := ⟨j.val - 5,by have := j.isLt; omega⟩
        have idj : j = tri i := Fin.ext (by change j.val = 5+(j.val-5); omega)
        rw [idj,row_move,tri_row,aTri,show (word t / 4294967296).testBit (ti k i).val = phase d ((word t / 4294967296).testBit i.val) from second_tri t l i,high,phase_comp]
  intro first suffix a b hFirst hSuffix hSize original originalWire hAb hBa hPos
  let f := fun (x : Fin 10 → Bool) => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
        (fun t => x (Fin.ofNat 10 (t / 10)) && x (Fin.ofNat 10 (t % 10)))
  let row := fun (j : Fin 15) (i : Fin 10) => ([116,201,402,554,773,50,69,104,138,208,276,385,521,548,770] : List ℕ).getD j.val 0 |>.testBit i.val
  have edge_eq (x : Fin 10 → Bool) : original x = f x := by
    change _ = ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any _
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    change _ = (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 ||
      (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 4 && x 9 ||
      (x 5 && x 7 || (x 7 && x 9 || (x 9 && x 6 || (x 6 && x 8 || x 8 && x 5))))))))))))))
    dsimp only [original]
    simp only [Bool.or_assoc]
  have row_false : ∀ j : Fin 15, f (row j) = false := by decide +kernel
  by_contra noWitness
  let C : Circuit := ⟨first :: suffix.gates, 0⟩
  let w := PEqualNP.CleanedNonEdge.wireVal 10 C
  have input (i : ℕ) (x : Fin 10 → Bool) : w i x = originalWire x i := rfl
  have hC : FanInTwo C := by
    intro g hg
    rcases List.mem_cons.mp hg with hg | hg
    · subst g; exact hFirst first List.mem_cons_self
    · exact hSuffix g hg
  have sz : C.size ≤ 18 := by
    change suffix.gates.length + 1 ≤ 18
    change suffix.gates.length ≤ 17 at hSize
    omega
  have exactPair : ∀ x, (w a x && w b x) = f x := by
    intro x
    rw [← edge_eq x, input, input]
    cases hx : original x with
    | false =>
      cases ha : originalWire x a <;> cases hb : originalWire x b
      · rfl
      · rfl
      · rfl
      · exact (noWitness ⟨x,hx,ha,hb⟩).elim
    | true =>
      obtain ⟨ha,hb⟩ := hPos x hx
      rw [ha,hb]; rfl
  obtain ⟨p,flip,tag,s,group,allowed,moveEdge,palette⟩ := colorOrbits (fun x => !(w a x))
  let index := fun (i : ℕ) => if h : i < 10 then (p ⟨i,h⟩).val else i
  let mapGate := fun (g : Gate) => (⟨g.op,g.inputs.map index⟩ : Gate)
  let D : Circuit := ⟨C.gates.map mapGate,0⟩
  let advance := fun (ws : List Bool) (g : Gate) => ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]
  have read_old (x : Fin 10 → Bool) (tail : List Bool) (i : ℕ) :
      (List.ofFn x ++ tail).getD (index i) false = (List.ofFn (x ∘ p) ++ tail).getD i false := by
    by_cases hi : i < 10
    · have hp : (p ⟨i,hi⟩).val < (List.ofFn x).length := by simpa using (p ⟨i,hi⟩).isLt
      have hj : i < (List.ofFn (x ∘ p)).length := by simpa using hi
      rw [show index i = (p ⟨i,hi⟩).val from dif_pos hi, List.getD_append _ _ _ _ hp,
        List.getD_append _ _ _ _ hj, List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ hj,
        List.getElem_ofFn, List.getElem_ofFn] <;> rfl
    · have h₁ : (List.ofFn x).length ≤ i := by simpa using Nat.le_of_not_gt hi
      have h₂ : (List.ofFn (x ∘ p)).length ≤ i := by simpa using Nat.le_of_not_gt hi
      simp only [index, dif_neg hi, List.getD_eq_getElem?_getD,
        List.getElem?_append_right h₁, List.getElem?_append_right h₂, List.length_ofFn]
  have fold (gs : List Gate) (x : Fin 10 → Bool) (tail : List Bool) :
      ∃ out : List Bool, (gs.map mapGate).foldl advance (List.ofFn x ++ tail) = List.ofFn x ++ out ∧
        gs.foldl advance (List.ofFn (x ∘ p) ++ tail) = List.ofFn (x ∘ p) ++ out := by
    induction gs generalizing tail with
    | nil => exact ⟨tail,rfl,rfl⟩
    | cons g gs ih =>
      let v := g.op.eval (g.inputs.map (fun i => (List.ofFn (x ∘ p) ++ tail).getD i false))
      have h₁ : advance (List.ofFn x ++ tail) (mapGate g) = List.ofFn x ++ (tail ++ [v]) := by
        simp only [advance,mapGate,List.map_map,Function.comp_def,read_old,List.append_assoc,v]
      have h₂ : advance (List.ofFn (x ∘ p) ++ tail) g = List.ofFn (x ∘ p) ++ (tail ++ [v]) := by
        simp only [advance,List.append_assoc,v]
      simpa only [List.map_cons,List.foldl_cons,h₁,h₂] using ih (tail ++ [v])
  let v := PEqualNP.CleanedNonEdge.wireVal 10 D
  have trans (i : ℕ) (x : Fin 10 → Bool) : v (index i) x = w i (x ∘ p) := by
    obtain ⟨out,h₁,h₂⟩ := fold C.gates x []
    simp only [List.append_nil] at h₁ h₂
    change ((C.gates.map mapGate).foldl advance (List.ofFn x)).getD (index i) false =
      (C.gates.foldl advance (List.ofFn (x ∘ p))).getD i false
    rw [h₁,h₂,read_old]
  have hD : FanInTwo D := by
    intro g hg
    obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hg
    obtain ⟨op,arity⟩ := hC old ho
    exact ⟨op,by simpa [mapGate] using arity⟩
  have sd : D.size ≤ 18 := by
    change (List.map mapGate C.gates).length ≤ 18
    rw [List.length_map]
    exact sz
  have undo (x : Fin 10 → Bool) : (x ∘ p.symm) ∘ p = x := by funext i; simp [Function.comp_def]
  have cab : ∃ x, v (index a) x = true ∧ v (index b) x = false := by
    obtain ⟨x,ha,hb⟩ := hAb
    exact ⟨x ∘ p.symm,by rw [trans,undo,input,ha],by rw [trans,undo,input,hb]⟩
  have cba : ∃ x, v (index a) x = false ∧ v (index b) x = true := by
    obtain ⟨x,ha,hb⟩ := hBa
    exact ⟨x ∘ p.symm,by rw [trans,undo,input,ha],by rw [trans,undo,input,hb]⟩
  have ce (x : Fin 10 → Bool) : (v (index a) x && v (index b) x) = f x := by
    rw [trans,trans,exactPair]
    exact moveEdge x
  let code := tag / 4294967296 * 32 + s.val
  let majority (s : Fin 32) : Bool := (4276676736 : ℕ).testBit s.val
  let tags : List ℕ := [2147516555,6451667119,16106189007,23803693775,33301789951,50209730747,58175753099,97442115771,67574152123,102827553023,126710677643,136109076667,170725002447,187619671983,205349965775,253419851567,479073438603,734439407659]
  have location : ∀ t ∈ tags, ∀ (s : Fin 32) (i : Fin 10), ∃ j : Fin 15,
      j.val < 5 ∧ (t / 4294967296 * 32 + s.val).testBit j.val = majority s ∧
      f (fun k : Fin 10 => (k == i) || row j k) = true := by decide +kernel
  have tagIn : tag ∈ tags := by
    change tag ∈ ([2147516555,6451667119,16106189007,23803693775] : List ℕ) ++ ([33301789951,50209730747,58175753099,97442115771] ++ [67574152123,102827553023,126710677643,136109076667,170725002447,187619671983,205349965775,253419851567,479073438603,734439407659])
    simpa only [List.mem_append] using group
  have bad (u t : ℕ) (h : ∀ j : Fin 15, (if code.testBit j.val then v u (row j) else v t (row j)) = false)
      (ht : ∃ x, v u x = true ∧ v t x = false) (hf : ∃ x, v u x = false ∧ v t x = true)
      (he : ∀ x, (v u x && v t x) = f x) : False := by
    have sensitive : ∀ i : Fin 10, ∃ j : Fin 15, j.val < 5 ∧
        v (if majority s then u else t) (row j) ≠ v (if majority s then u else t) (fun k : Fin 10 => (k == i) || row j k) := by
      intro i
      obtain ⟨j,hj,bits,pos⟩ := location tag tagIn s i
      change code.testBit j.val = majority s at bits
      have hzero := h j
      rw [bits] at hzero
      have z : v (if majority s then u else t) (row j) = false := by
        cases hm : majority s <;> simpa [hm] using hzero
      have pairTrue := Bool.and_eq_true_iff.mp ((he (fun k : Fin 10 => (k == i) || row j k)).trans pos)
      have o : v (if majority s then u else t) (fun k : Fin 10 => (k == i) || row j k) = true := by
        split
        · exact pairTrue.1
        · exact pairTrue.2
      exact ⟨j,hj,by rw [z,o]; decide⟩
    rcases group with htag | htag | htag
    · exact small D u t tag s hD sd htag allowed h ht hf sensitive he
    · exact middle D u t tag s hD sd htag allowed h ht hf sensitive he
    · exact large D u t tag s hD sd htag allowed h ht hf sensitive he
  have rowPair (j : Fin 15) : (v (index a) (row j) && v (index b) (row j)) = false :=
    (ce (row j)).trans (row_false j)
  have rowColor (j : Fin 15) : (!(v (index a) (row j))) = if flip then !(code.testBit j.val) else code.testBit j.val := by
    rw [trans]; exact palette j
  cases flip with
  | false =>
    refine bad (index a) (index b) ?_ cab cba ce
    intro j
    have hc := rowColor j
    have hr := rowPair j
    cases ht : code.testBit j.val <;> cases ha : v (index a) (row j) <;>
      cases hb : v (index b) (row j) <;> simp [ht,ha,hb] at hc hr ⊢
  | true =>
    refine bad (index b) (index a) ?_
      (by obtain ⟨x,h₁,h₂⟩ := cba; exact ⟨x,h₂,h₁⟩)
      (by obtain ⟨x,h₁,h₂⟩ := cab; exact ⟨x,h₂,h₁⟩)
      (fun x => (Bool.and_comm _ _).trans (ce x))
    intro j
    have hc := rowColor j
    have hr := rowPair j
    cases ht : code.testBit j.val <;> cases ha : v (index a) (row j) <;>
      cases hb : v (index b) (row j) <;> simp [ht,ha,hb] at hc hr ⊢
