import Tocio.YamlTotal

namespace Tocio

def splitLines (text : String) : List String := text.splitOn "\n"

def lineIndent (s : String) : Nat := s.toList.takeWhile (· = ' ') |>.length

def textToLines (text : String) : List YL2 :=
  (splitLines text).map (fun l => { indent := lineIndent l, text := l })

def parseYamlText (text : String) : Option YamlValue := parseYamlTotal (textToLines text)

end Tocio