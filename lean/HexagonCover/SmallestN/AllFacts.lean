import HexagonCover.SmallestN.Arithmetic
import HexagonCover.SmallestN.SupportRows

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.SmallestN.AllFacts
open Common Semantics

theorem checked (i : Fin 468) : CheckedFact i := by
  fin_cases i
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 0 (by decide +kernel) T contained
  · exact Arithmetic.checked_0001
  · exact Arithmetic.checked_0002
  · exact Arithmetic.checked_0003
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 4 (by decide +kernel) T contained
  · exact Arithmetic.checked_0005
  · exact Arithmetic.checked_0006
  · exact Arithmetic.checked_0007
  · exact Arithmetic.checked_0008
  · exact Arithmetic.checked_0009
  · exact Arithmetic.checked_0010
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 11 (by decide +kernel) T contained
  · exact Arithmetic.checked_0012
  · exact Arithmetic.checked_0013
  · exact Arithmetic.checked_0014
  · exact Arithmetic.checked_0015
  · exact Arithmetic.checked_0016
  · exact Arithmetic.checked_0017
  · exact Arithmetic.checked_0018
  · exact Arithmetic.checked_0019
  · exact Arithmetic.checked_0020
  · exact Arithmetic.checked_0021
  · exact Arithmetic.checked_0022
  · exact Arithmetic.checked_0023
  · exact Arithmetic.checked_0024
  · exact Arithmetic.checked_0025
  · exact Arithmetic.checked_0026
  · exact Arithmetic.checked_0027
  · exact Arithmetic.checked_0028
  · exact Arithmetic.checked_0029
  · exact Arithmetic.checked_0030
  · exact Arithmetic.checked_0031
  · exact Arithmetic.checked_0032
  · exact Arithmetic.checked_0033
  · exact Arithmetic.checked_0034
  · exact Arithmetic.checked_0035
  · exact Arithmetic.checked_0036
  · exact Arithmetic.checked_0037
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 38 (by decide +kernel) T contained
  · exact Arithmetic.checked_0039
  · exact Arithmetic.checked_0040
  · exact Arithmetic.checked_0041
  · exact Arithmetic.checked_0042
  · exact Arithmetic.checked_0043
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 44 (by decide +kernel) T contained
  · exact Arithmetic.checked_0045
  · exact Arithmetic.checked_0046
  · exact Arithmetic.checked_0047
  · exact Arithmetic.checked_0048
  · exact Arithmetic.checked_0049
  · exact Arithmetic.checked_0050
  · exact Arithmetic.checked_0051
  · exact Arithmetic.checked_0052
  · exact Arithmetic.checked_0053
  · exact Arithmetic.checked_0054
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 55 (by decide +kernel) T contained
  · exact Arithmetic.checked_0056
  · exact Arithmetic.checked_0057
  · exact Arithmetic.checked_0058
  · exact Arithmetic.checked_0059
  · exact Arithmetic.checked_0060
  · exact Arithmetic.checked_0061
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 62 (by decide +kernel) T contained
  · exact Arithmetic.checked_0063
  · exact Arithmetic.checked_0064
  · exact Arithmetic.checked_0065
  · exact Arithmetic.checked_0066
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 67 (by decide +kernel) T contained
  · exact Arithmetic.checked_0068
  · exact Arithmetic.checked_0069
  · exact Arithmetic.checked_0070
  · exact Arithmetic.checked_0071
  · exact Arithmetic.checked_0072
  · exact Arithmetic.checked_0073
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 74 (by decide +kernel) T contained
  · exact Arithmetic.checked_0075
  · exact Arithmetic.checked_0076
  · exact Arithmetic.checked_0077
  · exact Arithmetic.checked_0078
  · exact Arithmetic.checked_0079
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 80 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 81 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 82 (by decide +kernel) T contained
  · exact Arithmetic.checked_0083
  · exact Arithmetic.checked_0084
  · exact Arithmetic.checked_0085
  · exact Arithmetic.checked_0086
  · exact Arithmetic.checked_0087
  · exact Arithmetic.checked_0088
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 89 (by decide +kernel) T contained
  · exact Arithmetic.checked_0090
  · exact Arithmetic.checked_0091
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 92 (by decide +kernel) T contained
  · exact Arithmetic.checked_0093
  · exact Arithmetic.checked_0094
  · exact Arithmetic.checked_0095
  · exact Arithmetic.checked_0096
  · exact Arithmetic.checked_0097
  · exact Arithmetic.checked_0098
  · exact Arithmetic.checked_0099
  · exact Arithmetic.checked_0100
  · exact Arithmetic.checked_0101
  · exact Arithmetic.checked_0102
  · exact Arithmetic.checked_0103
  · exact Arithmetic.checked_0104
  · exact Arithmetic.checked_0105
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 106 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 107 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 108 (by decide +kernel) T contained
  · exact Arithmetic.checked_0109
  · exact Arithmetic.checked_0110
  · exact Arithmetic.checked_0111
  · exact Arithmetic.checked_0112
  · exact Arithmetic.checked_0113
  · exact Arithmetic.checked_0114
  · exact Arithmetic.checked_0115
  · exact Arithmetic.checked_0116
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 117 (by decide +kernel) T contained
  · exact Arithmetic.checked_0118
  · exact Arithmetic.checked_0119
  · exact Arithmetic.checked_0120
  · exact Arithmetic.checked_0121
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 122 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 123 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 124 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 125 (by decide +kernel) T contained
  · exact Arithmetic.checked_0126
  · exact Arithmetic.checked_0127
  · exact Arithmetic.checked_0128
  · exact Arithmetic.checked_0129
  · exact Arithmetic.checked_0130
  · exact Arithmetic.checked_0131
  · exact Arithmetic.checked_0132
  · exact Arithmetic.checked_0133
  · exact Arithmetic.checked_0134
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 135 (by decide +kernel) T contained
  · exact Arithmetic.checked_0136
  · exact Arithmetic.checked_0137
  · exact Arithmetic.checked_0138
  · exact Arithmetic.checked_0139
  · exact Arithmetic.checked_0140
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 141 (by decide +kernel) T contained
  · exact Arithmetic.checked_0142
  · exact Arithmetic.checked_0143
  · exact Arithmetic.checked_0144
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 145 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 146 (by decide +kernel) T contained
  · exact Arithmetic.checked_0147
  · exact Arithmetic.checked_0148
  · exact Arithmetic.checked_0149
  · exact Arithmetic.checked_0150
  · exact Arithmetic.checked_0151
  · exact Arithmetic.checked_0152
  · exact Arithmetic.checked_0153
  · exact Arithmetic.checked_0154
  · exact Arithmetic.checked_0155
  · exact Arithmetic.checked_0156
  · exact Arithmetic.checked_0157
  · exact Arithmetic.checked_0158
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 159 (by decide +kernel) T contained
  · exact Arithmetic.checked_0160
  · exact Arithmetic.checked_0161
  · exact Arithmetic.checked_0162
  · exact Arithmetic.checked_0163
  · exact Arithmetic.checked_0164
  · exact Arithmetic.checked_0165
  · exact Arithmetic.checked_0166
  · exact Arithmetic.checked_0167
  · exact Arithmetic.checked_0168
  · exact Arithmetic.checked_0169
  · exact Arithmetic.checked_0170
  · exact Arithmetic.checked_0171
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 172 (by decide +kernel) T contained
  · exact Arithmetic.checked_0173
  · exact Arithmetic.checked_0174
  · exact Arithmetic.checked_0175
  · exact Arithmetic.checked_0176
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 177 (by decide +kernel) T contained
  · exact Arithmetic.checked_0178
  · exact Arithmetic.checked_0179
  · exact Arithmetic.checked_0180
  · exact Arithmetic.checked_0181
  · exact Arithmetic.checked_0182
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 183 (by decide +kernel) T contained
  · exact Arithmetic.checked_0184
  · exact Arithmetic.checked_0185
  · exact Arithmetic.checked_0186
  · exact Arithmetic.checked_0187
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 188 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 189 (by decide +kernel) T contained
  · exact Arithmetic.checked_0190
  · exact Arithmetic.checked_0191
  · exact Arithmetic.checked_0192
  · exact Arithmetic.checked_0193
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 194 (by decide +kernel) T contained
  · exact Arithmetic.checked_0195
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 196 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 197 (by decide +kernel) T contained
  · exact Arithmetic.checked_0198
  · exact Arithmetic.checked_0199
  · exact Arithmetic.checked_0200
  · exact Arithmetic.checked_0201
  · exact Arithmetic.checked_0202
  · exact Arithmetic.checked_0203
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 204 (by decide +kernel) T contained
  · exact Arithmetic.checked_0205
  · exact Arithmetic.checked_0206
  · exact Arithmetic.checked_0207
  · exact Arithmetic.checked_0208
  · exact Arithmetic.checked_0209
  · exact Arithmetic.checked_0210
  · exact Arithmetic.checked_0211
  · exact Arithmetic.checked_0212
  · exact Arithmetic.checked_0213
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 214 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 215 (by decide +kernel) T contained
  · exact Arithmetic.checked_0216
  · exact Arithmetic.checked_0217
  · exact Arithmetic.checked_0218
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 219 (by decide +kernel) T contained
  · exact Arithmetic.checked_0220
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 221 (by decide +kernel) T contained
  · exact Arithmetic.checked_0222
  · exact Arithmetic.checked_0223
  · exact Arithmetic.checked_0224
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 225 (by decide +kernel) T contained
  · exact Arithmetic.checked_0226
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 227 (by decide +kernel) T contained
  · exact Arithmetic.checked_0228
  · exact Arithmetic.checked_0229
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 230 (by decide +kernel) T contained
  · exact Arithmetic.checked_0231
  · exact Arithmetic.checked_0232
  · exact Arithmetic.checked_0233
  · exact Arithmetic.checked_0234
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 235 (by decide +kernel) T contained
  · exact Arithmetic.checked_0236
  · exact Arithmetic.checked_0237
  · exact Arithmetic.checked_0238
  · exact Arithmetic.checked_0239
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 240 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 241 (by decide +kernel) T contained
  · exact Arithmetic.checked_0242
  · exact Arithmetic.checked_0243
  · exact Arithmetic.checked_0244
  · exact Arithmetic.checked_0245
  · exact Arithmetic.checked_0246
  · exact Arithmetic.checked_0247
  · exact Arithmetic.checked_0248
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 249 (by decide +kernel) T contained
  · exact Arithmetic.checked_0250
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 251 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 252 (by decide +kernel) T contained
  · exact Arithmetic.checked_0253
  · exact Arithmetic.checked_0254
  · exact Arithmetic.checked_0255
  · exact Arithmetic.checked_0256
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 257 (by decide +kernel) T contained
  · exact Arithmetic.checked_0258
  · exact Arithmetic.checked_0259
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 260 (by decide +kernel) T contained
  · exact Arithmetic.checked_0261
  · exact Arithmetic.checked_0262
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 263 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 264 (by decide +kernel) T contained
  · exact Arithmetic.checked_0265
  · exact Arithmetic.checked_0266
  · exact Arithmetic.checked_0267
  · exact Arithmetic.checked_0268
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 269 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 270 (by decide +kernel) T contained
  · exact Arithmetic.checked_0271
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 272 (by decide +kernel) T contained
  · exact Arithmetic.checked_0273
  · exact Arithmetic.checked_0274
  · exact Arithmetic.checked_0275
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 276 (by decide +kernel) T contained
  · exact Arithmetic.checked_0277
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 278 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 279 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 280 (by decide +kernel) T contained
  · exact Arithmetic.checked_0281
  · exact Arithmetic.checked_0282
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 283 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 284 (by decide +kernel) T contained
  · exact Arithmetic.checked_0285
  · exact Arithmetic.checked_0286
  · exact Arithmetic.checked_0287
  · exact Arithmetic.checked_0288
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 289 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 290 (by decide +kernel) T contained
  · exact Arithmetic.checked_0291
  · exact Arithmetic.checked_0292
  · exact Arithmetic.checked_0293
  · exact Arithmetic.checked_0294
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 295 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 296 (by decide +kernel) T contained
  · exact Arithmetic.checked_0297
  · exact Arithmetic.checked_0298
  · exact Arithmetic.checked_0299
  · exact Arithmetic.checked_0300
  · exact Arithmetic.checked_0301
  · exact Arithmetic.checked_0302
  · exact Arithmetic.checked_0303
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 304 (by decide +kernel) T contained
  · exact Arithmetic.checked_0305
  · exact Arithmetic.checked_0306
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 307 (by decide +kernel) T contained
  · exact Arithmetic.checked_0308
  · exact Arithmetic.checked_0309
  · exact Arithmetic.checked_0310
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 311 (by decide +kernel) T contained
  · exact Arithmetic.checked_0312
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 313 (by decide +kernel) T contained
  · exact Arithmetic.checked_0314
  · exact Arithmetic.checked_0315
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 316 (by decide +kernel) T contained
  · exact Arithmetic.checked_0317
  · exact Arithmetic.checked_0318
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 319 (by decide +kernel) T contained
  · exact Arithmetic.checked_0320
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 321 (by decide +kernel) T contained
  · exact Arithmetic.checked_0322
  · exact Arithmetic.checked_0323
  · exact Arithmetic.checked_0324
  · exact Arithmetic.checked_0325
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 326 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 327 (by decide +kernel) T contained
  · exact Arithmetic.checked_0328
  · exact Arithmetic.checked_0329
  · exact Arithmetic.checked_0330
  · exact Arithmetic.checked_0331
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 332 (by decide +kernel) T contained
  · exact Arithmetic.checked_0333
  · exact Arithmetic.checked_0334
  · exact Arithmetic.checked_0335
  · exact Arithmetic.checked_0336
  · exact Arithmetic.checked_0337
  · exact Arithmetic.checked_0338
  · exact Arithmetic.checked_0339
  · exact Arithmetic.checked_0340
  · exact Arithmetic.checked_0341
  · exact Arithmetic.checked_0342
  · exact Arithmetic.checked_0343
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 344 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 345 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 346 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 347 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 348 (by decide +kernel) T contained
  · exact Arithmetic.checked_0349
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 350 (by decide +kernel) T contained
  · exact Arithmetic.checked_0351
  · exact Arithmetic.checked_0352
  · exact Arithmetic.checked_0353
  · exact Arithmetic.checked_0354
  · exact Arithmetic.checked_0355
  · exact Arithmetic.checked_0356
  · exact Arithmetic.checked_0357
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 358 (by decide +kernel) T contained
  · exact Arithmetic.checked_0359
  · exact Arithmetic.checked_0360
  · exact Arithmetic.checked_0361
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 362 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 363 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 364 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 365 (by decide +kernel) T contained
  · exact Arithmetic.checked_0366
  · exact Arithmetic.checked_0367
  · exact Arithmetic.checked_0368
  · exact Arithmetic.checked_0369
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 370 (by decide +kernel) T contained
  · exact Arithmetic.checked_0371
  · exact Arithmetic.checked_0372
  · exact Arithmetic.checked_0373
  · exact Arithmetic.checked_0374
  · exact Arithmetic.checked_0375
  · exact Arithmetic.checked_0376
  · exact Arithmetic.checked_0377
  · exact Arithmetic.checked_0378
  · exact Arithmetic.checked_0379
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 380 (by decide +kernel) T contained
  · exact Arithmetic.checked_0381
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 382 (by decide +kernel) T contained
  · exact Arithmetic.checked_0383
  · exact Arithmetic.checked_0384
  · exact Arithmetic.checked_0385
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 386 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 387 (by decide +kernel) T contained
  · exact Arithmetic.checked_0388
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 389 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 390 (by decide +kernel) T contained
  · exact Arithmetic.checked_0391
  · exact Arithmetic.checked_0392
  · exact Arithmetic.checked_0393
  · exact Arithmetic.checked_0394
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 395 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 396 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 397 (by decide +kernel) T contained
  · exact Arithmetic.checked_0398
  · exact Arithmetic.checked_0399
  · exact Arithmetic.checked_0400
  · exact Arithmetic.checked_0401
  · exact Arithmetic.checked_0402
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 403 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 404 (by decide +kernel) T contained
  · exact Arithmetic.checked_0405
  · exact Arithmetic.checked_0406
  · exact Arithmetic.checked_0407
  · exact Arithmetic.checked_0408
  · exact Arithmetic.checked_0409
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 410 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 411 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 412 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 413 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 414 (by decide +kernel) T contained
  · exact Arithmetic.checked_0415
  · exact Arithmetic.checked_0416
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 417 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 418 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 419 (by decide +kernel) T contained
  · exact Arithmetic.checked_0420
  · exact Arithmetic.checked_0421
  · exact Arithmetic.checked_0422
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 423 (by decide +kernel) T contained
  · exact Arithmetic.checked_0424
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 425 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 426 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 427 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 428 (by decide +kernel) T contained
  · exact Arithmetic.checked_0429
  · exact Arithmetic.checked_0430
  · exact Arithmetic.checked_0431
  · exact Arithmetic.checked_0432
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 433 (by decide +kernel) T contained
  · exact Arithmetic.checked_0434
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 435 (by decide +kernel) T contained
  · exact Arithmetic.checked_0436
  · exact Arithmetic.checked_0437
  · exact Arithmetic.checked_0438
  · exact Arithmetic.checked_0439
  · exact Arithmetic.checked_0440
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 441 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 442 (by decide +kernel) T contained
  · exact Arithmetic.checked_0443
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 444 (by decide +kernel) T contained
  · exact Arithmetic.checked_0445
  · exact Arithmetic.checked_0446
  · exact Arithmetic.checked_0447
  · exact Arithmetic.checked_0448
  · exact Arithmetic.checked_0449
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 450 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 451 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 452 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 453 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 454 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 455 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 456 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 457 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 458 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 459 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 460 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 461 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 462 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 463 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 464 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 465 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 466 (by decide +kernel) T contained
  · refine ⟨?_⟩
    intro T contained _
    exact SupportRows.support_excluded 467 (by decide +kernel) T contained

#print axioms checked
end HexagonCover.SmallestN.AllFacts
