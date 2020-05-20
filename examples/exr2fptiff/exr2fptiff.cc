#include <cstdio>
#include <cstdlib>
#include <vector>

#include "tinyexr.h"

#define TINY_DNG_WRITER_IMPLEMENTATION
#include "tiny_dng_writer.h"

static bool Create32bitFpTiff(
  const float *data, // [width x height x in_channels]
  const size_t width,
  const size_t height,
  const size_t in_channels,
  const size_t channels,
  tinydngwriter::DNGImage *dng_image) {

  if (in_channels < 1) return false;

  unsigned int image_width = uint32_t(width);
  unsigned int image_height = uint32_t(height);

  //dng_image->SetSubfileType(false, false, false);
  dng_image->SetImageWidth(image_width);
  dng_image->SetImageLength(image_height);
  dng_image->SetRowsPerStrip(image_height);
  dng_image->SetSamplesPerPixel(uint16_t(channels));
  std::vector<uint16_t> bps(channels);
  for (size_t i = 0; i < bps.size(); i++) {
    bps[i] = 32;
  }
  dng_image->SetBitsPerSample(static_cast<unsigned int>(channels), bps.data());
  dng_image->SetPlanarConfig(tinydngwriter::PLANARCONFIG_CONTIG);
  dng_image->SetCompression(tinydngwriter::COMPRESSION_NONE);
  if (channels == 1) {
    dng_image->SetPhotometric(
        tinydngwriter::PHOTOMETRIC_BLACK_IS_ZERO);  // grayscale
  } else {
    dng_image->SetPhotometric(
        tinydngwriter::PHOTOMETRIC_RGB);
  }
  dng_image->SetXResolution(1.0);
  dng_image->SetYResolution(1.0);
  dng_image->SetResolutionUnit(tinydngwriter::RESUNIT_NONE);

  std::vector<uint16_t> formats(channels);
  for (size_t i = 0; i < formats.size(); i++) {
    formats[i] = tinydngwriter::SAMPLEFORMAT_IEEEFP;
  }
  dng_image->SetSampleFormat(static_cast<unsigned int>(channels), formats.data());

  std::vector<float> buf;
  buf.resize(size_t(channels) * image_width * image_height);

  for (size_t i = 0; i < image_width * image_height; i++) {
    size_t in_c = 0;
    for (size_t c = 0; c < channels; c++) {
      buf[channels * i + c] = data[in_channels * i + in_c];
      in_c++;
      in_c = std::min(in_c, in_channels - 1);
    }
  }

  //size_t max_dump_pixels = 4096;
  //for (size_t i = 0; i < std::min(max_dump_pixels, buf.size()); i++) {
  //  std::cout << "val[" << i << "] = " << buf[i] << "\n";
  //}
  //std::cout << "last = " << buf.at(image_width * image_height * channels - 1) << "\n";

  // We must retain pointer address of `buf` until calling DNGWriter::WriteToFile
  dng_image->SetImageData(reinterpret_cast<unsigned char *>(buf.data()),
                          buf.size() * sizeof(float));


  if (!dng_image->Error().empty()) {
    std::cout << "Err: " << dng_image->Error() << "\n";

    return false;
  }

  return true;
}

int main(int argc, char** argv)
{
  if (argc < 3) {
    printf("Usage: exr2fptiff input.exr output.tiff\n");
    exit(-1);
  }

  std::string input_filename = argv[1];
  std::string output_filename = argv[2];


  // Get # of layers
  size_t num_layers{0};
  {

    EXRVersion exr_version;
    {
      int ret = ParseEXRVersionFromFile(&exr_version, input_filename.c_str());
      if (ret != 0) {
        std::cerr << "Invalid EXR file: " << input_filename << "\n";
        return EXIT_FAILURE;
      }

      if (exr_version.multipart) {
        std::cerr << "Multipart EXR file is not supported in this example.\n";
        return EXIT_FAILURE;
      }
    }

    EXRHeader exr_header;
    InitEXRHeader(&exr_header);

    const char* err = nullptr;
    int ret = ParseEXRHeaderFromFile(&exr_header, &exr_version, argv[1], &err);
    if (ret != TINYEXR_SUCCESS) {
      if (err) {
        std::cerr << "Parse EXR error: " << err << "\n";
        FreeEXRErrorMessage(err); // free's buffer for an error message
      } else {
        std::cerr << "Parse EXR error.\n";
      }
      return EXIT_FAILURE;
    }

    num_layers = size_t(exr_header.num_channels);
    if (num_layers == 0) {
      std::cerr << "no layers found\n";
      return EXIT_FAILURE;
    }

    if (num_layers > 4) {
      std::cerr << "This program supports up to 4(e.g. RGBA) layers.\n";
      return EXIT_FAILURE;
    }

    FreeEXRHeader(&exr_header);
  }

  std::cout << "# of channels = " << num_layers << "\n";

  // Use legacy but easy-to-use API to read image.
  float *rgba{nullptr};
  int width;
  int height;
  {
    const char *err;
    int ret = LoadEXR(&rgba, &width, &height, input_filename.c_str(), &err);

    if (ret != TINYEXR_SUCCESS) {
      if (err) {
        std::cerr << "Load EXR error: " << err << "\n";
        FreeEXRErrorMessage(err); // free's buffer for an error message
      } else {
        std::cerr << "Load EXR error.\n";
      }
      return EXIT_FAILURE;
    }

  }

  bool big_endian = false;

  tinydngwriter::DNGImage tiff;
  tiff.SetBigEndian(big_endian);

  bool ret = Create32bitFpTiff(rgba, size_t(width), size_t(height), /* in_channels */4, size_t(num_layers), &tiff);
  if (!ret) {
    std::cerr << "Failed to create floating point tiff data\n";
    return EXIT_FAILURE;
  }

  // 4. Free image data
  free(rgba);

  tinydngwriter::DNGWriter dng_writer(big_endian);
  ret = dng_writer.AddImage(&tiff);
  if (!ret) {
    std::cerr << "Failed to add TIFF image to TIFF writer.\n";
    return EXIT_FAILURE;
  }

  // 5. write tiff
  std::string err;
  ret = dng_writer.WriteToFile(output_filename.c_str(), &err);

  if (!err.empty()) {
    std::cerr << err;
  }

  if (!ret) {
    return EXIT_FAILURE;
  }


  return EXIT_SUCCESS;
}
