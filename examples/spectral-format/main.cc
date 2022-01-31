#include <string>

// Reference: 
// An OpenEXR Layout for Spectral Images
// https://jcgt.org/published/0010/03/01/

/*
  layer = "((S[0-3])|T)"
  value = float(comma separated, optionally exponential)
  units = "(Y|Z|E|P|T|G|M|k|h|da|d|c|m|u|n|p|f|a|z|y)?(m|Hz)"
  regex = "^" + layer + '\.' + value + units + "$"
*/

enum Layer {
  LAYER_S0,
  LAYER_S1,
  LAYER_S2,
  LAYER_S3,
  LAYER_T
};
  
// for no polarization, S0 layer is used.
bool parse_layer(const std::string &s, Layer *layer_out, uint32_t *offset)
{
  
  Layer layer;
  if (s == "S0") {
    (*layer_out) = LAYER_S0;
    (*offset) = 2;
    return true;
  } else if (s == "S1") {
    (*layer_out) = LAYER_S1;
    (*offset) = 2;
    return true;
  } else if (s == "S2") {
    (*layer_out) = LAYER_S2;
    (*offset) = 2;
    return true;
  } else if (s == "S3") {
    (*layer_out) = LAYER_S3;
    (*offset) = 2;
    return true;
  } else if (s == "T") {
    (*layer_out) = LAYER_T;
    (*offset) = 1;
    return true;
  }

  return false;
}

bool parse_value(const std::string &s, double *value_out)
{
  // TODO: Implement
  return false;
}

bool parse_unit(const std::string &s, std::string *unit_out)
{
  std::string unit;

  // multipler
  if (s == "Y" ||
    (s == "Z") ||
    (s == "E") ||
    (s == "P") ||
    (s == "T") ||
    (s == "G") ||
    (s == "M") ||
    (s == "k") ||
    (s == "h") ||
    (s == "da") ||
    (s == "d") ||
    (s == "c") ||
    (s == "m") ||
    (s == "u") ||
    (s == "n") ||
    (s == "p") ||
    (s == "f") ||
    (s == "a") ||
    (s == "z") ||
    (s == "y")) {
    unit += s;
  }

  if (s == "m") {
    unit += s;
  } else if (s == "Hz") {
    unit += s;
  } else {
    // invalid
    return false;
  }

  (*unit_out) = unit;
  return true;
}

bool parse_channel(const std::string &name)
{
  uint32_t offt;
  std::string s = name;
  if (parse_layer(s,
}

int main(int argc, char **argv)
{

}
