import HexagonCover.DistanceData.Common

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.DistanceData.Batch0000
open HexagonCover.DistanceLeaf
open HexagonCover.DistanceData.Coordinates

def w00000 : CheckedWitness where
  data := {
    family := .q25
    factId := 0
    role := 0
    anchorId := 253
    pointIds := [253,0]
    points := [p0216,p0000]
    positions := (0,1)
    originalFlag := false
    journalLine := 1
    identity := "bc1f8eec2ed31785ea509b604670ac834cb49264afa0728e48f4ca66fa8e6e82" }
  checked := by decide +kernel

theorem w00000_check : checkWitness w00000.data.points w00000.data.positions = true :=
  w00000.checked

def w00001 : CheckedWitness where
  data := {
    family := .q25
    factId := 1
    role := 1
    anchorId := 254
    pointIds := [254,0]
    points := [p0116,p0000]
    positions := (0,1)
    originalFlag := false
    journalLine := 2
    identity := "d327a2e9d3ffe42930a4e5bd029ce57cc235cc32bb18f80a60e14685dc6c3f35" }
  checked := by decide +kernel

theorem w00001_check : checkWitness w00001.data.points w00001.data.positions = true :=
  w00001.checked

def w00002 : CheckedWitness where
  data := {
    family := .q25
    factId := 2
    role := 5
    anchorId := 258
    pointIds := [258,0]
    points := [p0208,p0000]
    positions := (0,1)
    originalFlag := false
    journalLine := 3
    identity := "ed9c396543527ac7e04a704afe6abc1ae9009bed0d803771511b03f45fb370a6" }
  checked := by decide +kernel

theorem w00002_check : checkWitness w00002.data.points w00002.data.positions = true :=
  w00002.checked

def w00003 : CheckedWitness where
  data := {
    family := .q25
    factId := 3
    role := 0
    anchorId := 253
    pointIds := [253,1]
    points := [p0216,p0001]
    positions := (0,1)
    originalFlag := false
    journalLine := 4
    identity := "20b63487095e379f882b9f1f7ab900f03b0bbe092e8865a99b99fcff10620bad" }
  checked := by decide +kernel

theorem w00003_check : checkWitness w00003.data.points w00003.data.positions = true :=
  w00003.checked

def w00004 : CheckedWitness where
  data := {
    family := .q25
    factId := 4
    role := 1
    anchorId := 254
    pointIds := [254,1]
    points := [p0116,p0001]
    positions := (0,1)
    originalFlag := false
    journalLine := 5
    identity := "dae8ebdbcdbd30b760046bca7d876775899503faf5a82403c85c0ba765fd0801" }
  checked := by decide +kernel

theorem w00004_check : checkWitness w00004.data.points w00004.data.positions = true :=
  w00004.checked

def w00005 : CheckedWitness where
  data := {
    family := .q25
    factId := 5
    role := 4
    anchorId := 257
    pointIds := [257,1]
    points := [p0100,p0001]
    positions := (0,1)
    originalFlag := false
    journalLine := 6
    identity := "724858040e0969c49787efd67e9b5ef62f1877995b549d5abb0a67cc6dae03d3" }
  checked := by decide +kernel

theorem w00005_check : checkWitness w00005.data.points w00005.data.positions = true :=
  w00005.checked

def w00006 : CheckedWitness where
  data := {
    family := .q25
    factId := 6
    role := 5
    anchorId := 258
    pointIds := [258,1]
    points := [p0208,p0001]
    positions := (0,1)
    originalFlag := false
    journalLine := 7
    identity := "dd82c016f51396fbf036064f97f2848b511ba2ebd681c50302163c57aa09efba" }
  checked := by decide +kernel

theorem w00006_check : checkWitness w00006.data.points w00006.data.positions = true :=
  w00006.checked

def w00007 : CheckedWitness where
  data := {
    family := .q25
    factId := 7
    role := 0
    anchorId := 253
    pointIds := [253,2]
    points := [p0216,p0002]
    positions := (0,1)
    originalFlag := false
    journalLine := 8
    identity := "446167f686f48466f612e343754999972db4f17697270b2e50315b17ce9e3413" }
  checked := by decide +kernel

theorem w00007_check : checkWitness w00007.data.points w00007.data.positions = true :=
  w00007.checked

def w00008 : CheckedWitness where
  data := {
    family := .q25
    factId := 8
    role := 1
    anchorId := 254
    pointIds := [254,2]
    points := [p0116,p0002]
    positions := (0,1)
    originalFlag := false
    journalLine := 9
    identity := "083aa8d0d2a58767fdee9f4ee81e2d84cc5b4dc2b693e8c133f6ee5e7dd5e269" }
  checked := by decide +kernel

theorem w00008_check : checkWitness w00008.data.points w00008.data.positions = true :=
  w00008.checked

def w00009 : CheckedWitness where
  data := {
    family := .q25
    factId := 9
    role := 4
    anchorId := 257
    pointIds := [257,2]
    points := [p0100,p0002]
    positions := (0,1)
    originalFlag := false
    journalLine := 10
    identity := "5b3e9c8a83aa7114f7f3afaeea09ba278803f6a43e3771385380c1c3c58d06c6" }
  checked := by decide +kernel

theorem w00009_check : checkWitness w00009.data.points w00009.data.positions = true :=
  w00009.checked

def w00010 : CheckedWitness where
  data := {
    family := .q25
    factId := 10
    role := 5
    anchorId := 258
    pointIds := [258,2]
    points := [p0208,p0002]
    positions := (0,1)
    originalFlag := false
    journalLine := 11
    identity := "859c4d881c48a0698e0e5eaeb86b305bb147aabbcc49bbbd485fcdf3d91f3862" }
  checked := by decide +kernel

theorem w00010_check : checkWitness w00010.data.points w00010.data.positions = true :=
  w00010.checked

def w00011 : CheckedWitness where
  data := {
    family := .q25
    factId := 11
    role := 0
    anchorId := 253
    pointIds := [253,3]
    points := [p0216,p0003]
    positions := (0,1)
    originalFlag := false
    journalLine := 12
    identity := "e859cca72211270076506493bc709b0c6852fd9664475fb395c096a7257861ea" }
  checked := by decide +kernel

theorem w00011_check : checkWitness w00011.data.points w00011.data.positions = true :=
  w00011.checked

def w00012 : CheckedWitness where
  data := {
    family := .q25
    factId := 12
    role := 1
    anchorId := 254
    pointIds := [254,3]
    points := [p0116,p0003]
    positions := (0,1)
    originalFlag := false
    journalLine := 13
    identity := "c98d75f26209edda338404fc9fadc18798d11739c733cb7c038f730476980632" }
  checked := by decide +kernel

theorem w00012_check : checkWitness w00012.data.points w00012.data.positions = true :=
  w00012.checked

def w00013 : CheckedWitness where
  data := {
    family := .q25
    factId := 13
    role := 4
    anchorId := 257
    pointIds := [257,3]
    points := [p0100,p0003]
    positions := (0,1)
    originalFlag := false
    journalLine := 14
    identity := "5e0e2659ea4c89d0571eee7820ba41a7082a9a2c8f939338715b49248675c8bf" }
  checked := by decide +kernel

theorem w00013_check : checkWitness w00013.data.points w00013.data.positions = true :=
  w00013.checked

def w00014 : CheckedWitness where
  data := {
    family := .q25
    factId := 14
    role := 5
    anchorId := 258
    pointIds := [258,3]
    points := [p0208,p0003]
    positions := (0,1)
    originalFlag := false
    journalLine := 15
    identity := "cf815b041d555640b1dee2e78a7d1d6ea32ec83bcf7e2530ce3e13f8c058a4e5" }
  checked := by decide +kernel

theorem w00014_check : checkWitness w00014.data.points w00014.data.positions = true :=
  w00014.checked

def w00015 : CheckedWitness where
  data := {
    family := .q25
    factId := 15
    role := 0
    anchorId := 253
    pointIds := [253,4]
    points := [p0216,p0004]
    positions := (0,1)
    originalFlag := false
    journalLine := 16
    identity := "c9cd5217cd5a9623e5424dfdaa092161b6e282de181edd91a67f275d6ad671d9" }
  checked := by decide +kernel

theorem w00015_check : checkWitness w00015.data.points w00015.data.positions = true :=
  w00015.checked

def w00016 : CheckedWitness where
  data := {
    family := .q25
    factId := 16
    role := 1
    anchorId := 254
    pointIds := [254,4]
    points := [p0116,p0004]
    positions := (0,1)
    originalFlag := false
    journalLine := 17
    identity := "ca3a8b8e780a424826b83c9054c52528e90ba895ab8cf7b665017381a14fdd3e" }
  checked := by decide +kernel

theorem w00016_check : checkWitness w00016.data.points w00016.data.positions = true :=
  w00016.checked

def w00017 : CheckedWitness where
  data := {
    family := .q25
    factId := 17
    role := 4
    anchorId := 257
    pointIds := [257,4]
    points := [p0100,p0004]
    positions := (0,1)
    originalFlag := false
    journalLine := 18
    identity := "7f3e66539903561f4f8dd91ace0b43088df48d4c4729c49c45413c4babf0ff6a" }
  checked := by decide +kernel

theorem w00017_check : checkWitness w00017.data.points w00017.data.positions = true :=
  w00017.checked

def w00018 : CheckedWitness where
  data := {
    family := .q25
    factId := 18
    role := 5
    anchorId := 258
    pointIds := [258,4]
    points := [p0208,p0004]
    positions := (0,1)
    originalFlag := false
    journalLine := 19
    identity := "0357d0e8470e822aa7ec1297d104af6820d499c32f5ded37db63e58e093403b5" }
  checked := by decide +kernel

theorem w00018_check : checkWitness w00018.data.points w00018.data.positions = true :=
  w00018.checked

def w00019 : CheckedWitness where
  data := {
    family := .q25
    factId := 19
    role := 0
    anchorId := 253
    pointIds := [253,5]
    points := [p0216,p0005]
    positions := (0,1)
    originalFlag := false
    journalLine := 20
    identity := "5cd39b08cf862ef3c83131a1db36fcf0074a294fe1e2d8559b9252abfe07d656" }
  checked := by decide +kernel

theorem w00019_check : checkWitness w00019.data.points w00019.data.positions = true :=
  w00019.checked

def w00020 : CheckedWitness where
  data := {
    family := .q25
    factId := 20
    role := 1
    anchorId := 254
    pointIds := [254,5]
    points := [p0116,p0005]
    positions := (0,1)
    originalFlag := false
    journalLine := 21
    identity := "cbfefe8fcb40cc96705d57695e2afd81ed98d48094cf1087fca74cbdd28973e9" }
  checked := by decide +kernel

theorem w00020_check : checkWitness w00020.data.points w00020.data.positions = true :=
  w00020.checked

def w00021 : CheckedWitness where
  data := {
    family := .q25
    factId := 21
    role := 4
    anchorId := 257
    pointIds := [257,5]
    points := [p0100,p0005]
    positions := (0,1)
    originalFlag := false
    journalLine := 22
    identity := "08c1125b96ed8dac113a8ef8bc2bb51343d40cd8073c5145699f8b61cda792a3" }
  checked := by decide +kernel

theorem w00021_check : checkWitness w00021.data.points w00021.data.positions = true :=
  w00021.checked

def w00022 : CheckedWitness where
  data := {
    family := .q25
    factId := 22
    role := 5
    anchorId := 258
    pointIds := [258,5]
    points := [p0208,p0005]
    positions := (0,1)
    originalFlag := false
    journalLine := 23
    identity := "31f046eaafe2f81fe3eb768b5a156846b27036049894ed34d255e0f15c70292c" }
  checked := by decide +kernel

theorem w00022_check : checkWitness w00022.data.points w00022.data.positions = true :=
  w00022.checked

def w00023 : CheckedWitness where
  data := {
    family := .q25
    factId := 23
    role := 0
    anchorId := 253
    pointIds := [253,6]
    points := [p0216,p0006]
    positions := (0,1)
    originalFlag := false
    journalLine := 24
    identity := "4b1306d337d842072056e9f06560c63ebdf25bfd61562a5eb1447ccf97806889" }
  checked := by decide +kernel

theorem w00023_check : checkWitness w00023.data.points w00023.data.positions = true :=
  w00023.checked

def w00024 : CheckedWitness where
  data := {
    family := .q25
    factId := 24
    role := 1
    anchorId := 254
    pointIds := [254,6]
    points := [p0116,p0006]
    positions := (0,1)
    originalFlag := false
    journalLine := 25
    identity := "e94f27a50461931ee6b2804ac9ffce6f158f7859035d8709ecd5f17da226942e" }
  checked := by decide +kernel

theorem w00024_check : checkWitness w00024.data.points w00024.data.positions = true :=
  w00024.checked

def w00025 : CheckedWitness where
  data := {
    family := .q25
    factId := 25
    role := 4
    anchorId := 257
    pointIds := [257,6]
    points := [p0100,p0006]
    positions := (0,1)
    originalFlag := false
    journalLine := 26
    identity := "ac216b1aca7d49147d3ddba55c99913cf0582ae9f15ae4233fa45109cecd2272" }
  checked := by decide +kernel

theorem w00025_check : checkWitness w00025.data.points w00025.data.positions = true :=
  w00025.checked

def w00026 : CheckedWitness where
  data := {
    family := .q25
    factId := 26
    role := 5
    anchorId := 258
    pointIds := [258,6]
    points := [p0208,p0006]
    positions := (0,1)
    originalFlag := false
    journalLine := 27
    identity := "a7234f06b66649e3b35006b5403f7010372155c9dc7f8a7153cada7cabf60f65" }
  checked := by decide +kernel

theorem w00026_check : checkWitness w00026.data.points w00026.data.positions = true :=
  w00026.checked

def w00027 : CheckedWitness where
  data := {
    family := .q25
    factId := 27
    role := 0
    anchorId := 253
    pointIds := [253,7]
    points := [p0216,p0007]
    positions := (0,1)
    originalFlag := false
    journalLine := 28
    identity := "67db82b0746d2688135c02be6bd6fda790b0e6539d56d1c1d8146062effca474" }
  checked := by decide +kernel

theorem w00027_check : checkWitness w00027.data.points w00027.data.positions = true :=
  w00027.checked

def w00028 : CheckedWitness where
  data := {
    family := .q25
    factId := 28
    role := 1
    anchorId := 254
    pointIds := [254,7]
    points := [p0116,p0007]
    positions := (0,1)
    originalFlag := false
    journalLine := 29
    identity := "d409b790559ccbebd91711b8884e0d46ffc2d8c3e8ee8ae2aed3548b8224f4ef" }
  checked := by decide +kernel

theorem w00028_check : checkWitness w00028.data.points w00028.data.positions = true :=
  w00028.checked

def w00029 : CheckedWitness where
  data := {
    family := .q25
    factId := 29
    role := 4
    anchorId := 257
    pointIds := [257,7]
    points := [p0100,p0007]
    positions := (0,1)
    originalFlag := false
    journalLine := 30
    identity := "901177c9444198074761a66bf383cc74faea32bb3f6b326a21a6638e33cfc86c" }
  checked := by decide +kernel

theorem w00029_check : checkWitness w00029.data.points w00029.data.positions = true :=
  w00029.checked

def w00030 : CheckedWitness where
  data := {
    family := .q25
    factId := 30
    role := 5
    anchorId := 258
    pointIds := [258,7]
    points := [p0208,p0007]
    positions := (0,1)
    originalFlag := false
    journalLine := 31
    identity := "9ee536775581533852a5327e6724138dbfea3e907a7ee70d8a85835059a75386" }
  checked := by decide +kernel

theorem w00030_check : checkWitness w00030.data.points w00030.data.positions = true :=
  w00030.checked

def w00031 : CheckedWitness where
  data := {
    family := .q25
    factId := 31
    role := 0
    anchorId := 253
    pointIds := [253,8]
    points := [p0216,p0008]
    positions := (0,1)
    originalFlag := false
    journalLine := 32
    identity := "cb287157b176a71c876bfd95b667a52a502e898e9f1fc04afb8aed590b581dc5" }
  checked := by decide +kernel

theorem w00031_check : checkWitness w00031.data.points w00031.data.positions = true :=
  w00031.checked

def w00032 : CheckedWitness where
  data := {
    family := .q25
    factId := 32
    role := 4
    anchorId := 257
    pointIds := [257,8]
    points := [p0100,p0008]
    positions := (0,1)
    originalFlag := false
    journalLine := 33
    identity := "666298f5a8f44279339176685efba381c5ab73fa126655b9cba8804910682d8c" }
  checked := by decide +kernel

theorem w00032_check : checkWitness w00032.data.points w00032.data.positions = true :=
  w00032.checked

def w00033 : CheckedWitness where
  data := {
    family := .q25
    factId := 33
    role := 5
    anchorId := 258
    pointIds := [258,8]
    points := [p0208,p0008]
    positions := (0,1)
    originalFlag := false
    journalLine := 34
    identity := "50b62c47b1c00721ad092982bfdd5cf7b358e527c14b5313e2b5c7e0a5ce3b04" }
  checked := by decide +kernel

theorem w00033_check : checkWitness w00033.data.points w00033.data.positions = true :=
  w00033.checked

def w00034 : CheckedWitness where
  data := {
    family := .q25
    factId := 34
    role := 0
    anchorId := 253
    pointIds := [253,9]
    points := [p0216,p0009]
    positions := (0,1)
    originalFlag := false
    journalLine := 35
    identity := "c9ca0fc0cec09f199d332ebccd91c43744fb97de4752c80fb963f4b4702c2a6d" }
  checked := by decide +kernel

theorem w00034_check : checkWitness w00034.data.points w00034.data.positions = true :=
  w00034.checked

def w00035 : CheckedWitness where
  data := {
    family := .q25
    factId := 35
    role := 1
    anchorId := 254
    pointIds := [254,9]
    points := [p0116,p0009]
    positions := (0,1)
    originalFlag := false
    journalLine := 36
    identity := "d45e5f83ad250316db989b4b1fa4cbe14756017bfe4399d404a58b906613fff5" }
  checked := by decide +kernel

theorem w00035_check : checkWitness w00035.data.points w00035.data.positions = true :=
  w00035.checked

def w00036 : CheckedWitness where
  data := {
    family := .q25
    factId := 36
    role := 2
    anchorId := 255
    pointIds := [255,9]
    points := [p0008,p0009]
    positions := (0,1)
    originalFlag := false
    journalLine := 37
    identity := "53f0defebfcc19190264ea9182c14a5441eef5b9bb941b5514a9187bb865fb5a" }
  checked := by decide +kernel

theorem w00036_check : checkWitness w00036.data.points w00036.data.positions = true :=
  w00036.checked

def w00037 : CheckedWitness where
  data := {
    family := .q25
    factId := 37
    role := 5
    anchorId := 258
    pointIds := [258,9]
    points := [p0208,p0009]
    positions := (0,1)
    originalFlag := false
    journalLine := 38
    identity := "154f74761a5cb10ccd14dcc334e1d59cfaa0e0571a38982d3eb04a2c2a78b579" }
  checked := by decide +kernel

theorem w00037_check : checkWitness w00037.data.points w00037.data.positions = true :=
  w00037.checked

def w00038 : CheckedWitness where
  data := {
    family := .q25
    factId := 38
    role := 0
    anchorId := 253
    pointIds := [253,10]
    points := [p0216,p0010]
    positions := (0,1)
    originalFlag := false
    journalLine := 39
    identity := "3ff1b68fb6ff6f56ff2bf66c5277f8c3373b85d9a1842424516dce90436972ae" }
  checked := by decide +kernel

theorem w00038_check : checkWitness w00038.data.points w00038.data.positions = true :=
  w00038.checked

def w00039 : CheckedWitness where
  data := {
    family := .q25
    factId := 39
    role := 1
    anchorId := 254
    pointIds := [254,10]
    points := [p0116,p0010]
    positions := (0,1)
    originalFlag := false
    journalLine := 40
    identity := "186ffd7e3cc4eca30d109900ed8086eb08535124fcd3b505884c725ba48083c8" }
  checked := by decide +kernel

theorem w00039_check : checkWitness w00039.data.points w00039.data.positions = true :=
  w00039.checked

def w00040 : CheckedWitness where
  data := {
    family := .q25
    factId := 40
    role := 5
    anchorId := 258
    pointIds := [258,10]
    points := [p0208,p0010]
    positions := (0,1)
    originalFlag := false
    journalLine := 41
    identity := "2ca999c3f77175a46a8f63ecf1eb58a9b7548a100dc07adaa8d83c5212b1e5b0" }
  checked := by decide +kernel

theorem w00040_check : checkWitness w00040.data.points w00040.data.positions = true :=
  w00040.checked

def w00041 : CheckedWitness where
  data := {
    family := .q25
    factId := 41
    role := 0
    anchorId := 253
    pointIds := [253,11]
    points := [p0216,p0011]
    positions := (0,1)
    originalFlag := false
    journalLine := 42
    identity := "66d3c3a68051ab31ff40c75c7812a2742c27fb2b0f44c1c48d3ddc8f8c799011" }
  checked := by decide +kernel

theorem w00041_check : checkWitness w00041.data.points w00041.data.positions = true :=
  w00041.checked

def w00042 : CheckedWitness where
  data := {
    family := .q25
    factId := 42
    role := 1
    anchorId := 254
    pointIds := [254,11]
    points := [p0116,p0011]
    positions := (0,1)
    originalFlag := false
    journalLine := 43
    identity := "d950a87fba29b5663da2e534043f014352e3ebd7d70454e6155a673e5e696de0" }
  checked := by decide +kernel

theorem w00042_check : checkWitness w00042.data.points w00042.data.positions = true :=
  w00042.checked

def w00043 : CheckedWitness where
  data := {
    family := .q25
    factId := 43
    role := 4
    anchorId := 257
    pointIds := [257,11]
    points := [p0100,p0011]
    positions := (0,1)
    originalFlag := false
    journalLine := 44
    identity := "8accac5d6589f5e4e80081c2a4009fca798dad7336625c1c1016614205f3acc8" }
  checked := by decide +kernel

theorem w00043_check : checkWitness w00043.data.points w00043.data.positions = true :=
  w00043.checked

def w00044 : CheckedWitness where
  data := {
    family := .q25
    factId := 44
    role := 5
    anchorId := 258
    pointIds := [258,11]
    points := [p0208,p0011]
    positions := (0,1)
    originalFlag := false
    journalLine := 45
    identity := "3555246801ca9150141e03ba25680cf958ef7133dbe03f78babe5ef957440ae7" }
  checked := by decide +kernel

theorem w00044_check : checkWitness w00044.data.points w00044.data.positions = true :=
  w00044.checked

def w00045 : CheckedWitness where
  data := {
    family := .q25
    factId := 45
    role := 0
    anchorId := 253
    pointIds := [253,12]
    points := [p0216,p0012]
    positions := (0,1)
    originalFlag := false
    journalLine := 46
    identity := "dcc6cf65ee342073c5310e38f50133b705d87804a75d310dc2f3d14937fd3303" }
  checked := by decide +kernel

theorem w00045_check : checkWitness w00045.data.points w00045.data.positions = true :=
  w00045.checked

def w00046 : CheckedWitness where
  data := {
    family := .q25
    factId := 46
    role := 1
    anchorId := 254
    pointIds := [254,12]
    points := [p0116,p0012]
    positions := (0,1)
    originalFlag := false
    journalLine := 47
    identity := "4138145b33e18a9c13813ea7fcf9e834425d6358f5109f8db1ae652442208d43" }
  checked := by decide +kernel

theorem w00046_check : checkWitness w00046.data.points w00046.data.positions = true :=
  w00046.checked

def w00047 : CheckedWitness where
  data := {
    family := .q25
    factId := 47
    role := 4
    anchorId := 257
    pointIds := [257,12]
    points := [p0100,p0012]
    positions := (0,1)
    originalFlag := false
    journalLine := 48
    identity := "86832e4f76bcec459f164680ad2fa9ea362ecad33a57150e39a56673f7ecf85d" }
  checked := by decide +kernel

theorem w00047_check : checkWitness w00047.data.points w00047.data.positions = true :=
  w00047.checked

def w00048 : CheckedWitness where
  data := {
    family := .q25
    factId := 48
    role := 5
    anchorId := 258
    pointIds := [258,12]
    points := [p0208,p0012]
    positions := (0,1)
    originalFlag := false
    journalLine := 49
    identity := "aeaf8c5ee10627087929525d15576cfe16bd776568875a99882f24d30df5f5c7" }
  checked := by decide +kernel

theorem w00048_check : checkWitness w00048.data.points w00048.data.positions = true :=
  w00048.checked

def w00049 : CheckedWitness where
  data := {
    family := .q25
    factId := 49
    role := 0
    anchorId := 253
    pointIds := [253,13]
    points := [p0216,p0013]
    positions := (0,1)
    originalFlag := false
    journalLine := 50
    identity := "afc213aade76cbe826ba64e3aff7845998c6789a7ce11fed26cba6715811a4f4" }
  checked := by decide +kernel

theorem w00049_check : checkWitness w00049.data.points w00049.data.positions = true :=
  w00049.checked

def w00050 : CheckedWitness where
  data := {
    family := .q25
    factId := 50
    role := 1
    anchorId := 254
    pointIds := [254,13]
    points := [p0116,p0013]
    positions := (0,1)
    originalFlag := false
    journalLine := 51
    identity := "86a4d7d0682be34d91c130911e9e4430253a8f272fc6c5118d097acf32aa4be8" }
  checked := by decide +kernel

theorem w00050_check : checkWitness w00050.data.points w00050.data.positions = true :=
  w00050.checked

def w00051 : CheckedWitness where
  data := {
    family := .q25
    factId := 51
    role := 4
    anchorId := 257
    pointIds := [257,13]
    points := [p0100,p0013]
    positions := (0,1)
    originalFlag := false
    journalLine := 52
    identity := "b41db4cd19a9f653fff6b90b725a18e2a04492d51da7bd9234db6bc2ec8cae3c" }
  checked := by decide +kernel

theorem w00051_check : checkWitness w00051.data.points w00051.data.positions = true :=
  w00051.checked

def w00052 : CheckedWitness where
  data := {
    family := .q25
    factId := 52
    role := 5
    anchorId := 258
    pointIds := [258,13]
    points := [p0208,p0013]
    positions := (0,1)
    originalFlag := false
    journalLine := 53
    identity := "eb9b2be3a93b06b698c44b05d425f59773fd6ff7bc1f47851e0f22f328d8b258" }
  checked := by decide +kernel

theorem w00052_check : checkWitness w00052.data.points w00052.data.positions = true :=
  w00052.checked

def w00053 : CheckedWitness where
  data := {
    family := .q25
    factId := 53
    role := 0
    anchorId := 253
    pointIds := [253,14]
    points := [p0216,p0014]
    positions := (0,1)
    originalFlag := false
    journalLine := 54
    identity := "6d987b23f0ee7b6f50c08d136aa2384f29043cd477452ce923d65c17d55ca54a" }
  checked := by decide +kernel

theorem w00053_check : checkWitness w00053.data.points w00053.data.positions = true :=
  w00053.checked

def w00054 : CheckedWitness where
  data := {
    family := .q25
    factId := 54
    role := 1
    anchorId := 254
    pointIds := [254,14]
    points := [p0116,p0014]
    positions := (0,1)
    originalFlag := false
    journalLine := 55
    identity := "bdbd20bc5baef16e0589c56c39236f5fdf1f66911a7ddd2de2b5fcfbc2067c03" }
  checked := by decide +kernel

theorem w00054_check : checkWitness w00054.data.points w00054.data.positions = true :=
  w00054.checked

def w00055 : CheckedWitness where
  data := {
    family := .q25
    factId := 55
    role := 4
    anchorId := 257
    pointIds := [257,14]
    points := [p0100,p0014]
    positions := (0,1)
    originalFlag := false
    journalLine := 56
    identity := "53a262d2067358934935bbc4f6ade99840600ee33eb50707451b17f2eaa1f82a" }
  checked := by decide +kernel

theorem w00055_check : checkWitness w00055.data.points w00055.data.positions = true :=
  w00055.checked

def w00056 : CheckedWitness where
  data := {
    family := .q25
    factId := 56
    role := 5
    anchorId := 258
    pointIds := [258,14]
    points := [p0208,p0014]
    positions := (0,1)
    originalFlag := false
    journalLine := 57
    identity := "fcb7e01f3cc1ec3b6e8f2ccade88ade7e02ceec70d4b6b16d338f64a0357a783" }
  checked := by decide +kernel

theorem w00056_check : checkWitness w00056.data.points w00056.data.positions = true :=
  w00056.checked

def w00057 : CheckedWitness where
  data := {
    family := .q25
    factId := 57
    role := 0
    anchorId := 253
    pointIds := [253,15]
    points := [p0216,p0015]
    positions := (0,1)
    originalFlag := false
    journalLine := 58
    identity := "574a9248d2742d32f98989f4501df4145c86c0ae29b1f9b31a42090dec2b7de2" }
  checked := by decide +kernel

theorem w00057_check : checkWitness w00057.data.points w00057.data.positions = true :=
  w00057.checked

def w00058 : CheckedWitness where
  data := {
    family := .q25
    factId := 58
    role := 1
    anchorId := 254
    pointIds := [254,15]
    points := [p0116,p0015]
    positions := (0,1)
    originalFlag := false
    journalLine := 59
    identity := "6d03aa2360ebc34198c602208d341ae7aad887a57f803ba029e28edcac02a5d5" }
  checked := by decide +kernel

theorem w00058_check : checkWitness w00058.data.points w00058.data.positions = true :=
  w00058.checked

def w00059 : CheckedWitness where
  data := {
    family := .q25
    factId := 59
    role := 4
    anchorId := 257
    pointIds := [257,15]
    points := [p0100,p0015]
    positions := (0,1)
    originalFlag := false
    journalLine := 60
    identity := "0a95846d528547ec69f7525489f2179a44ee39c31e9ec97ba931066ec9ba33a0" }
  checked := by decide +kernel

theorem w00059_check : checkWitness w00059.data.points w00059.data.positions = true :=
  w00059.checked

def w00060 : CheckedWitness where
  data := {
    family := .q25
    factId := 60
    role := 5
    anchorId := 258
    pointIds := [258,15]
    points := [p0208,p0015]
    positions := (0,1)
    originalFlag := false
    journalLine := 61
    identity := "f64f34779bc9647b936d20bf4c493b44a319ba76783ebf13fe34cf220f6acd3e" }
  checked := by decide +kernel

theorem w00060_check : checkWitness w00060.data.points w00060.data.positions = true :=
  w00060.checked

def w00061 : CheckedWitness where
  data := {
    family := .q25
    factId := 61
    role := 0
    anchorId := 253
    pointIds := [253,16]
    points := [p0216,p0016]
    positions := (0,1)
    originalFlag := false
    journalLine := 62
    identity := "5fb6cdcdda12ba213bfed74d7b36ad0d80e68df6f5e334e7a19cb43478dd7300" }
  checked := by decide +kernel

theorem w00061_check : checkWitness w00061.data.points w00061.data.positions = true :=
  w00061.checked

def w00062 : CheckedWitness where
  data := {
    family := .q25
    factId := 62
    role := 1
    anchorId := 254
    pointIds := [254,16]
    points := [p0116,p0016]
    positions := (0,1)
    originalFlag := false
    journalLine := 63
    identity := "57488756988e83e6fb86c17ceab30067f85d1d5c719508c7be6cece445fa3cab" }
  checked := by decide +kernel

theorem w00062_check : checkWitness w00062.data.points w00062.data.positions = true :=
  w00062.checked

def w00063 : CheckedWitness where
  data := {
    family := .q25
    factId := 63
    role := 4
    anchorId := 257
    pointIds := [257,16]
    points := [p0100,p0016]
    positions := (0,1)
    originalFlag := false
    journalLine := 64
    identity := "cfa8b66505a48e8930d71ab6d1bfc1789b1d06fbe281963e60f87fa5fe3031be" }
  checked := by decide +kernel

theorem w00063_check : checkWitness w00063.data.points w00063.data.positions = true :=
  w00063.checked

def rows : List CheckedWitness := [w00000,w00001,w00002,w00003,w00004,w00005,w00006,w00007,w00008,w00009,w00010,w00011,w00012,w00013,w00014,w00015,w00016,w00017,w00018,w00019,w00020,w00021,w00022,w00023,w00024,w00025,w00026,w00027,w00028,w00029,w00030,w00031,w00032,w00033,w00034,w00035,w00036,w00037,w00038,w00039,w00040,w00041,w00042,w00043,w00044,w00045,w00046,w00047,w00048,w00049,w00050,w00051,w00052,w00053,w00054,w00055,w00056,w00057,w00058,w00059,w00060,w00061,w00062,w00063]

theorem checked_count : rows.length = 64 := by decide +kernel

theorem all_excluded (w : CheckedWitness) (_hw : w ∈ rows) (T : UnitTriangle) :
    ¬ (∀ p, p ∈ w.data.points → toPlane p ∈ T.region) :=
  w.excluded T

end HexagonCover.DistanceData.Batch0000
