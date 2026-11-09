import Tocio.YamlTotal

namespace Tocio

def splitLines (text : String) : List String := text.splitOn "\n"

def lineIndent (s : String) : Nat := s.toList.takeWhile (· = ' ') |>.length

def textToLines (text : String) : List YL2 :=
  (splitLines text).map (fun l => { indent := lineIndent l, text := l })

def parseYamlText (text : String) : Option YamlValue := parseYamlTotalV (textToLines text)

-- Backward-compat alias name used by earlier scaffolding.
def parseYamlTotal (lines : List YL2) : Option YamlValue := parseYamlTotalV lines

end Tocio