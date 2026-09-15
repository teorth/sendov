import Sendov.Common.DistillationPeakAlgebra
import Sendov.Common.BernsteinList

/-!
# Joint elementary, zeroth and second peak budget

The actual elementary loss remains in the joint numerator. The only split is
`a = 5/2`, where the legal degree floor `max 5 (2 a)` changes formula.
The common positive denominator is factored, not separately recertified by data.
Both degree-47 identities are full symbolic identities.
-/

namespace Sendov.PeakClosure

def jointDen (a : ℝ) : ℝ :=
  a * S a ^ 3 * F a ^ 3 * D a ^ 3 * t6 ((2 * a - 3) * F a) (G a)

def gapLow (a : ℝ) : ℝ :=
  (3125 * (1819 + 3 * a) * a * S a ^ 3 * F a ^ 3 * D a ^ 3 -
    3906250 * N a * a * S a ^ 3 * F a ^ 2 * D a ^ 3 -
    78125 * N a * a * F a ^ 3 * D a ^ 3 -
    23437500000 * S a ^ 12 * N a * J a * F a) *
      t6 ((2 * a - 3) * F a) (G a) -
    1263 * N a * a * G a ^ 8 * (6723 * G a + 5416 * a * F a) * D a ^ 3

def gapHigh (a : ℝ) : ℝ :=
  (37500 * (2069 + 3 * a) * a * S a ^ 3 * F a ^ 3 * D a ^ 3 -
    46875000 * N a * a * S a ^ 3 * F a ^ 2 * D a ^ 3 -
    781250 * N a * a * F a ^ 3 * D a ^ 3 -
    23437500 * S a ^ 3 * F a ^ 3 * D a ^ 3 -
    390625 * N a * F a ^ 3 * D a ^ 3 -
    281250000000 * S a ^ 12 * N a * J a * F a) *
      t6 ((2 * a - 3) * F a) (G a) -
    15156 * N a * a * G a ^ 8 * (6723 * G a + 5416 * a * F a) * D a ^ 3

lemma jointDen_pos {a : ℝ} (ha : 2 ≤ a) : 0 < jointDen a := by
  have ha0 : 0 < a := by linarith
  have := S_pos ha0.le
  have := F_pos ha0.le
  have := D_pos ha0.le
  have := t6_pos (mul_nonneg (by linarith : 0 ≤ 2 * a - 3) (F_pos ha0.le).le)
    (G_pos ha0.le)
  unfold jointDen
  positivity

namespace LowHomogeneous

private def SH (x y : ℝ) : ℝ :=
  10 * x ^ 0 * y ^ 1 +
    11 * x ^ 1 * y ^ 0

private lemma SH_eval (a : ℝ) :
    SH (a - (2)) ((5 / 2) - a) = (1 : ℝ) ^ 1 * S a := by
  unfold SH S
  ring1

private def NH (x y : ℝ) : ℝ :=
  2984 * x ^ 0 * y ^ 2 +
    6560 * x ^ 1 * y ^ 1 +
    3605 * x ^ 2 * y ^ 0

private lemma NH_eval (a : ℝ) :
    NH (a - (2)) ((5 / 2) - a) = (1 : ℝ) ^ 2 * N a := by
  unfold NH N
  ring1

private def FH (x y : ℝ) : ℝ :=
  18064 * x ^ 0 * y ^ 3 +
    57840 * x ^ 1 * y ^ 2 +
    61680 * x ^ 2 * y ^ 1 +
    21905 * x ^ 3 * y ^ 0

private lemma FH_eval (a : ℝ) :
    FH (a - (2)) ((5 / 2) - a) = (1 : ℝ) ^ 3 * F a := by
  unfold FH F
  ring1

private def GH (x y : ℝ) : ℝ :=
  41936 * x ^ 0 * y ^ 3 +
    140160 * x ^ 1 * y ^ 2 +
    156120 * x ^ 2 * y ^ 1 +
    57955 * x ^ 3 * y ^ 0

private lemma GH_eval (a : ℝ) :
    GH (a - (2)) ((5 / 2) - a) = (1 : ℝ) ^ 3 * G a := by
  unfold GH G
  ring1

private def DH (x y : ℝ) : ℝ :=
  30064 * x ^ 0 * y ^ 3 +
    97440 * x ^ 1 * y ^ 2 +
    105240 * x ^ 2 * y ^ 1 +
    37877 * x ^ 3 * y ^ 0

private lemma DH_eval (a : ℝ) :
    DH (a - (2)) ((5 / 2) - a) = (1 : ℝ) ^ 3 * D a := by
  unfold DH D
  ring1

private def JH (x y : ℝ) : ℝ :=
  370024 * x ^ 0 * y ^ 3 +
    1192740 * x ^ 1 * y ^ 2 +
    1280910 * x ^ 2 * y ^ 1 +
    458291 * x ^ 3 * y ^ 0

private lemma JH_eval (a : ℝ) :
    JH (a - (2)) ((5 / 2) - a) = (1 : ℝ) ^ 3 * J a := by
  unfold JH J
  ring1

private def gapH (x y : ℝ) : ℝ :=
  let z := 2 * (x + y)
  let b := 4 * y + 5 * x
  (3125 * (1819 * z + 3 * b) * b * SH x y ^ 3 * FH x y ^ 3 * DH x y ^ 3 -
    3906250 * NH x y * b * SH x y ^ 3 * FH x y ^ 2 * DH x y ^ 3 * z ^ 2 -
    78125 * NH x y * b * FH x y ^ 3 * DH x y ^ 3 * z ^ 2 -
    23437500000 * SH x y ^ 12 * NH x y * JH x y * FH x y * z ^ 3) *
      t6 ((2 * b - 3 * z) * FH x y) (z * GH x y) -
    1263 * NH x y * b * GH x y ^ 8 *
      (6723 * z * GH x y + 5416 * b * FH x y) * DH x y ^ 3 * z ^ 7

lemma gapH_eval (a : ℝ) :
    gapH (a - (2)) ((5 / 2) - a) = ((
      1 : ℕ) : ℝ) *
        gapLow a := by
  simp only [gapH, SH_eval, NH_eval, FH_eval, GH_eval, DH_eval, JH_eval, gapLow, t6]
  ring1

private def coefficients : List ℕ := [
  28687231504364325032601869723445872447324983311445964958222241497088,
  1582470884517134842005578612798484747555273639928136326122746727628800,
  42477829560992384110457357641481089857017906878222887289408281531908096,
  739991578476397822350133939211373380355778117354268774703542562566701056,
  9413056885932049870437637478252909243026309772882846488332131468700549120,
  93259940190499531365813802273382087026148329770609094431054491175094321152,
  749539208821165482212556144974311598775954155184881940423498769820729475072,
  5025372953230470851603705598134768560851621417453752029150285206160750411776,
  28684166640670678720610795626886932213461246102393460985085922710453881929728,
  141544969138884429935199086884156019328301955943379069193957333728179313967104,
  611124284151271312951680838948273121743113432252944266568872236811165498343424,
  2330742211495422210000371809035441859034996959347844184354516459847036157558784,
  7913118499797015740820645764620857398698511393389031236153638377710097056923648,
  24068259216899798379936780097112061908794032084695043266207876399632757651668992,
  65927147281600083878921306654440298932116167269213663699969656108563848362983424,
  163343579680054264119016704303494996095477788761035850187562927529953345174241280,
  367399152474887375258818525464220139846670110057649222598139207215170501017075712,
  752467859247056995005469226570004271805252877364236588967368830685456973072171008,
  1406826797146415829777186918022572530531674453024353094076907086287186041021399040,
  2405959481954287992874670889022213600437904499583786002855449434275520321222082560,
  3770060987352898880800496304527756880079991851711283552530241676376910606379253760,
  5419763555231114745387210724756725643299658804399850355843612224285665928203468800,
  7154813405295885141357741777609942561035753064005586741861237951689744842122854400,
  8679203016865827929555737960166472908771393043255280752648083208088018031424307200,
  9677688796304807537487224868595559320860485875723491095168351701590420335099904000,
  9919560979140861407140764221408805965530862362201975948826830116308272117972992000,
  9344007104242418535060402014428743351940565228821383000965233647273311295504384000,
  8084522500401051069413653872882556660981281341114489775913986947660535667097600000,
  6419201881448217165480050637481674686619500186383036996160079087352699677573120000,
  4671904617346067820478084781558798986878505898618824791272607705180349836820480000,
  3111844057281932459124149980408328558999479112769005716989570734786471254425600000,
  1893235729991851904124545466179602166252040127507429990399742458557930828595200000,
  1049572191719473385576995180348682865783662511689356966436931752106906289766400000,
  528658776562341975608520513624753559156398321757735009396005846763394307072000000,
  241083845995078020324569217631158852444003062607738421599393810014024053248000000,
  99118250239934318950638058737191121765552404630525003992731219602567597568000000,
  36552543805101490210009236757568708960228515464282651981395671477024749440000000,
  12016463630234911404315522706739364181578208779840803401088451340248756720000000,
  3495034251891797117533347510852352645931861409668474362881041778889108960000000,
  891014717301182519594129731897207490989285870737328430887812389171836200000000,
  196776904713778175247836913887350781998096992539491612454184666225621600000000,
  37081511583502455897700811627099733565496914219000961361725918870410575000000,
  5844457308382822406737113797001111478146048246405193318972811272136250000000,
  749465611683340016524487419973964294090193344954173279767878731087250000000,
  75108892506493962283330837008673969319966623994864334005032500279000000000,
  5517771459967244556976623417418409705597878753861436193715382705000000000,
  264262424414129340280092119033185949135450991396339212985779130000000000,
  6191237285816150279084488283919823436327247079696528432958912500000000]

lemma gapH_identity (x y : ℝ) :
    gapH x y = (BernsteinCert.coeffTree coefficients 0).eval x y := by
  simp only [gapH, SH, NH, FH, GH, DH, JH, t6]
  simp only [coefficients, BernsteinCert.coeffTree_eval_cons,
    BernsteinCert.coeffTree_eval_nil, List.length_cons, List.length_nil, Nat.cast_ofNat]
  ring1

lemma identity (a : ℝ) :
    ((
      1 : ℕ) : ℝ) * gapLow a =
      (BernsteinCert.coeffTree coefficients 0).eval (a - (2)) ((5 / 2) - a) := by
  rw [← gapH_eval]
  exact gapH_identity (a - (2)) ((5 / 2) - a)

lemma positive {a : ℝ} (ha : a ∈ Set.Icc (2) (5 / 2)) : 0 < gapLow a := by
  exact BernsteinCert.coeffs_pos coefficients
    (by norm_num) (by norm_num) ha (by decide) (by decide) (identity a)

end LowHomogeneous

lemma gapLow_pos {a : ℝ} (ha : a ∈ Set.Icc (2) (5 / 2)) : 0 < gapLow a :=
  LowHomogeneous.positive ha

namespace HighHomogeneous

private def SH (x y : ℝ) : ℝ :=
  11 * x ^ 0 * y ^ 1 +
    40 * x ^ 1 * y ^ 0

private lemma SH_eval (a : ℝ) :
    SH (a - (5 / 2)) ((17) - a) = (29 : ℝ) ^ 1 * S a := by
  unfold SH S
  ring1

private def NH (x y : ℝ) : ℝ :=
  3605 * x ^ 0 * y ^ 2 +
    26060 * x ^ 1 * y ^ 1 +
    46844 * x ^ 2 * y ^ 0

private lemma NH_eval (a : ℝ) :
    NH (a - (5 / 2)) ((17) - a) = (29 : ℝ) ^ 2 * N a := by
  unfold NH N
  ring1

private def FH (x y : ℝ) : ℝ :=
  21905 * x ^ 0 * y ^ 3 +
    182730 * x ^ 1 * y ^ 2 +
    463740 * x ^ 2 * y ^ 1 +
    327304 * x ^ 3 * y ^ 0

private lemma FH_eval (a : ℝ) :
    FH (a - (5 / 2)) ((17) - a) = (29 : ℝ) ^ 3 * F a := by
  unfold FH F
  ring1

private def GH (x y : ℝ) : ℝ :=
  57955 * x ^ 0 * y ^ 3 +
    688470 * x ^ 1 * y ^ 2 +
    2704260 * x ^ 2 * y ^ 1 +
    3512696 * x ^ 3 * y ^ 0

private lemma GH_eval (a : ℝ) :
    GH (a - (5 / 2)) ((17) - a) = (29 : ℝ) ^ 3 * G a := by
  unfold GH G
  ring1

private def DH (x y : ℝ) : ℝ :=
  37877 * x ^ 0 * y ^ 3 +
    356970 * x ^ 1 * y ^ 2 +
    1097340 * x ^ 2 * y ^ 1 +
    1095304 * x ^ 3 * y ^ 0

private lemma DH_eval (a : ℝ) :
    DH (a - (5 / 2)) ((17) - a) = (29 : ℝ) ^ 3 * D a := by
  unfold DH D
  ring1

private def JH (x y : ℝ) : ℝ :=
  458291 * x ^ 0 * y ^ 3 +
    4099800 * x ^ 1 * y ^ 2 +
    11696640 * x ^ 2 * y ^ 1 +
    10420864 * x ^ 3 * y ^ 0

private lemma JH_eval (a : ℝ) :
    JH (a - (5 / 2)) ((17) - a) = (29 : ℝ) ^ 3 * J a := by
  unfold JH J
  ring1

private def gapH (x y : ℝ) : ℝ :=
  let z := 2 * (x + y)
  let b := 5 * y + 34 * x
  (37500 * (2069 * z + 3 * b) * b * SH x y ^ 3 * FH x y ^ 3 * DH x y ^ 3 -
    46875000 * NH x y * b * SH x y ^ 3 * FH x y ^ 2 * DH x y ^ 3 * z ^ 2 -
    781250 * NH x y * b * FH x y ^ 3 * DH x y ^ 3 * z ^ 2 -
    23437500 * SH x y ^ 3 * FH x y ^ 3 * DH x y ^ 3 * z ^ 2 -
    390625 * NH x y * FH x y ^ 3 * DH x y ^ 3 * z ^ 3 -
    281250000000 * SH x y ^ 12 * NH x y * JH x y * FH x y * z ^ 3) *
      t6 ((2 * b - 3 * z) * FH x y) (z * GH x y) -
    15156 * NH x y * b * GH x y ^ 8 *
      (6723 * z * GH x y + 5416 * b * FH x y) * DH x y ^ 3 * z ^ 7

lemma gapH_eval (a : ℝ) :
    gapH (a - (5 / 2)) ((17) - a) = ((
      540388254896363906423085056139791027545489078221423373035998591883509 : ℕ) : ℝ) *
        gapHigh a := by
  simp only [gapH, SH_eval, NH_eval, FH_eval, GH_eval, DH_eval, JH_eval, gapHigh, t6]
  ring1

private def coefficients : List ℕ := [
  74294847429793803349013859407037881235926964956358341195506950000000000,
  14468208523937467153670902052811485558859630976644137123669912260000000000,
  1309708807098842653716700406222379534304225015994802129176540772660000000000,
  74576457150190025865884332417107464369000959506932847067298507871628000000000,
  3030009977994709507138115055555654561058159449596267705652585055169167000000000,
  94164843289451615331819486290514185117021666479379122457933828894412865000000000,
  2338896013483961737783309734508401854205591013417248627312817349583556984900000000,
  47851339751446162416440976260342841871497987003987991767961397439404805959200000000,
  824172647663660612853666662698174188106257796449610304950444419780873663948400000000,
  12148548122904954743774949073833696799998311384788259957721744326406135934618120000000,
  155220161070734422173392420798761486753974195177357558906127723174067036401905440000000,
  1736492319202497447856104544825467294091336616840954077643834057986773684210885280000000,
  17148467155199067861106782667584716076083624695486481181619446020262917450330713856000000,
  150478921147515391939367188838979676759198636841351498715082418779485919641451070336000000,
  1179716947516088028938178044676109848067198859264191898097937905939586165117452706304000000,
  8299843940765309666079249593351913658220338946458170469628423963609898491257495982796800000,
  52595464470677421110964717678212998990487783069914630531976855981621412766058717718118400000,
  301108036953314661533878180546489045715314383381276266715033302046829649770108860224307200000,
  1561191043554546394894831604065622283283013701261834176737775314116271878622481590076047360000,
  7345126477852844153535053183494006142839812725944103816616514838775134137294792831004835840000,
  0x3c3975c2d89444a1c18d9318c8552df40faa3554b2960c36cb38cf911cc91bd3a83a63475000000,
  0xea487ad98073ee3a5b92dd064f7e8756b1ddb7a551ba30f9a63982e57cf46cbac273cbf39800000,
  0x33dd5f9c08e545e9219df45bd7ef8a7715a58ec06641b355ebe66b18e1469ee4277d619d24000000,
  0xa7555c35f2e2c9730cd74ae67189d4270870ba1815c1f8f81f0c113083fb89586231e05c36000000,
  0x1ebcb537004f4f4cbf971277b735cbf14a1bce576eb0b88c3ea968c3a9e04ed57a788cc4e08000000,
  0x524522f25952727ebd84178df7104530f847d19643abae95ddc4ea52b1896366bad37c5147c000000,
  0xc86b871dcfb9120a0773a92f6498547c2099fe71ec30cae997e57d752ae9ed8bb75c0e084b0000000,
  0x1bbf8fdec8d836821576da17a3f15156defdbf88830ea5451fefbbe71b48ee5ed6eb7f8c4330000000,
  0x37d274e2980cf6446be1b7dde12232810623791b8df8a2169388d9f358dffd46986c375d4280000000,
  0x65d01cc1d3c83b50da11e30f64c7a1fddcc9e45f3dafa0ff8cd4771c5f7f2cf16ae8c4d0ee40000000,
  0xa800aaa099bae249b06b4002e31fdccce357b447a360985ee42ce637725fedbb073d9b0e5700000000,
  0xfa2ad7c5f8e1d46c3fd8fa330fd5b3d0e1b0d434eeb2febda595212f80a951995cd767ef9500000000,
  0x14f1eb0b3123fceb64af1ad765db1324765ee35bddf096d35da446989a31918e81603d2a07000000000,
  0x1925abf3004db72ae84bc1731116c43a5a54aa5993d055e5e9f16163004b81b89619bf9180800000000,
  0x1af0b69370affe541a973699e57ff3dfa225992bbf857bcd66ecdf63d7127e395c04a662be000000000,
  0x199d8afb01564cc50282df5c72bed9edbbef112815331523e083df7ed31d36f6f7ab5f0e62000000000,
  0x157a584fa6375082c77005ebcdac068a091df5a7e57d1d627daa8c1721e650da39e4458170000000000,
  0xfc1dd159f1902822f921bbc841cde2af8eb7364698946964d94f2471e7cd59cf15b75d1d8000000000,
  0xa04b48f933caf70c6971a023f9bff5330299756b744b04076f11de13d48af30493e7ee170000000000,
  0x5744538ba9be0df2d1194c4df47a5b14816c3217605555005fbe24694c011e72099826360000000000,
  0x28102b43f779da7d506a5bcf425170203dd7bcad959b8461d4a8530af6ac7ea11977f8dc0000000000,
  0xf336638b15c6494498e2bfaab6acd7740d140a58cd96aa59ee983d927a1cc13bbd0c5820000000000,
  0x4a32f162a8a76964c9954f78392f015ab3e432b43a95511166cc6e212274f52556dae880000000000,
  0x117e8eb0cb76aa8e29e5441c9aa6e9c3d68deec4602157897cb2069d5016987275fc8280000000000,
  0x2ff1d654ae0967c9f0e70060409c55b36674d050ddb321e66626a0b2a3f808a94dd1c00000000000,
  0x5585178654fab3c4cddc25ab697ff05301f10bda4e3ba7676984e4556f6b17e1048e00000000000,
  2519500525180673896491860843808907330553020264601599548769406599846561391488288736450571141120,
  19286492509041959506496627214548384489747573868937787217081427690416394743856453359077687296]

lemma gapH_identity (x y : ℝ) :
    gapH x y = (BernsteinCert.coeffTree coefficients 0).eval x y := by
  simp only [gapH, SH, NH, FH, GH, DH, JH, t6]
  simp only [coefficients, BernsteinCert.coeffTree_eval_cons,
    BernsteinCert.coeffTree_eval_nil, List.length_cons, List.length_nil, Nat.cast_ofNat]
  ring1

lemma identity (a : ℝ) :
    ((
      540388254896363906423085056139791027545489078221423373035998591883509 : ℕ) : ℝ) * gapHigh a =
      (BernsteinCert.coeffTree coefficients 0).eval (a - (5 / 2)) ((17) - a) := by
  rw [← gapH_eval]
  exact gapH_identity (a - (5 / 2)) ((17) - a)

lemma positive {a : ℝ} (ha : a ∈ Set.Icc (5 / 2) (17)) : 0 < gapHigh a := by
  exact BernsteinCert.coeffs_pos coefficients
    (by norm_num) (by norm_num) ha (by decide) (by decide) (identity a)

end HighHomogeneous

lemma gapHigh_pos {a : ℝ} (ha : a ∈ Set.Icc (5 / 2) (17)) : 0 < gapHigh a :=
  HighHomogeneous.positive ha

lemma gapLow_eq {a : ℝ} (ha : 2 ≤ a) :
    1 - budget1 a - distillElementary 5 a - distillPeak0 a -
        numerator2 a / denominator2 a = gapLow a / (7812500 * jointDen a) := by
  have ha0 : 0 < a := by linarith
  rw [elementary_eq ha0.le, peak0_eq ha0]
  have hs := (S_pos ha0.le).ne'
  have hf := (F_pos ha0.le).ne'
  have hd := (D_pos ha0.le).ne'
  have ht := (t6_pos
    (mul_nonneg (by linarith : 0 ≤ 2 * a - 3) (F_pos ha0.le).le) (G_pos ha0.le)).ne'
  unfold budget1 numerator2 denominator2 gapLow jointDen
  generalize t6 ((2 * a - 3) * F a) (G a) = t at ht ⊢
  field_simp [ht]
  ring

lemma gapHigh_eq {a : ℝ} (ha : 2 ≤ a) :
    1 - budget1 a - distillElementary (2 * a) a - distillPeak0 a -
        numerator2 a / denominator2 a = gapHigh a / (93750000 * jointDen a) := by
  have ha0 : 0 < a := by linarith
  rw [elementary_eq ha0.le, peak0_eq ha0]
  have hs := (S_pos ha0.le).ne'
  have hf := (F_pos ha0.le).ne'
  have hd := (D_pos ha0.le).ne'
  have ht := (t6_pos
    (mul_nonneg (by linarith : 0 ≤ 2 * a - 3) (F_pos ha0.le).le) (G_pos ha0.le)).ne'
  unfold budget1 numerator2 denominator2 gapHigh jointDen
  generalize t6 ((2 * a - 3) * F a) (G a) = t at ht ⊢
  field_simp [ht]
  ring

lemma rest_lt_budget {a : ℝ} (ha : 2 ≤ a) (h17 : a ≤ 17) :
    distillElementary (max 5 (2 * a)) a + distillPeak0 a +
        (421 / 12500) * distillRatio a *
          distillRationalExpPeak a (distillPeakRate2 a) (distillPeakRate2 a * (2 * a - 3)) <
      1 - budget1 a := by
  rw [peak2_eq ha]
  by_cases hcut : a ≤ 5 / 2
  · rw [max_eq_left (by linarith : 2 * a ≤ 5)]
    have h := div_pos (gapLow_pos ⟨ha, hcut⟩)
      (mul_pos (by norm_num : (0 : ℝ) < 7812500) (jointDen_pos ha))
    rw [← gapLow_eq ha] at h
    linarith
  · rw [max_eq_right (by linarith : 5 ≤ 2 * a)]
    have h := div_pos (gapHigh_pos ⟨by linarith, h17⟩)
      (mul_pos (by norm_num : (0 : ℝ) < 93750000) (jointDen_pos ha))
    rw [← gapHigh_eq ha] at h
    linarith

end Sendov.PeakClosure
