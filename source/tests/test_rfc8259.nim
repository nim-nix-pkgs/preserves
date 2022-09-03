# SPDX-FileCopyrightText: 2021 ☭ Emery Hemingway
# SPDX-License-Identifier: Unlicense

import preserves, preserves/jsonhooks
import std/[json, jsonutils, streams, unittest]

let testVectors = [
"""
{
  "Image": {
    "Width": 800,
    "Height": 600,
    "Title": "View from 15th Floor",
    "Thumbnail": {
      "Url": "http://www.example.com/image/481989943",
      "Height": 125,
      "Width": 100
    },
    "Animated": false,
    "IDs": [
      116,
      943,
      234,
      38793
    ]
  }
}
""",
"""
[
  {
    "space": "C3D2",
    "logo": "https://www.c3d2.de/images/ck.png",
    "url": "https://www.c3d2.de/",
    "location": {
      "address": "Raum 1.04.01, Haus B, Zentralwerk, Riesaer Straße 32, 01127 Dresden, Germany",
      "lat": 51.0810791,
      "lon": 13.7286123
    }
  },
  {
    "space": "LAG",
    "logo": "http://laglab.org/logo.png",
    "url": "http://laglab.org",
    "location": {
      "address": "Eerste Schinkelstraat 16, 1075 TX Amsterdam, The Netherlands",
      "lat": 52.35406,
      "lon": 4.85423
    }
  }
]
"""
]

for i, jsText in testVectors:
  test $i:
    checkpoint(jsText)
    let
      control = parseJson jsText
      x = control.toPreserve
    checkpoint($x)
    var stream = newStringStream()
    stream.write(x)
    stream.setPosition(0)
    let
      y = stream.decodePreserves()
      test = y.toJson
    check(y == x)
    check(test == control)
