import OpenEXR
import Imath
import numpy as np
import simpleimageio as sio

width = 420
height = 32
border_left = 0
border_right = 420 - 80
num_splats = 10000

red = np.zeros((height, width), dtype=np.float32)
green = np.zeros((height, width), dtype=np.float32)
blue = np.zeros((height, width), dtype=np.float32)

# splat random color values
rng = np.random.default_rng()
row = rng.integers(low=0, high=height, size=num_splats)
col = rng.integers(low=border_left, high=border_right, size=num_splats)

# if any of the three channels has a fixed value, the problem goes away!
red[row, col] = rng.random(num_splats)
green[row, col] = rng.random(num_splats)
blue[row, col] = rng.random(num_splats)

# add a bunch of test pixels
red[-8, -10] = 1
green[-8, -10] = 1
blue[-8, -10] = 1

red[-4, -8] = 1
green[-4, -8] = 1
blue[-4, -8] = 1

red[-4, -2] = 1
green[-4, -2] = 1
blue[-4, -2] = 1

red[-2, -3] = 0 # setting this to anything other than 0 fixes the problem
green[-2, -3] = 1
blue[-2, -3] = 1

# fill in all of the black region with 0-red color
# red[:,border_right:] = 0
# green[:,border_right:] = 1
# blue[:,border_right:] = 1

# write PIZ compressed via OpenEXR
header = OpenEXR.Header(width, height)
header['compression'] = Imath.Compression(Imath.Compression.PIZ_COMPRESSION)
exr = OpenEXR.OutputFile("gen.exr", header)
exr.writePixels({'R': red.tobytes(), 'G': green.tobytes(), 'B': blue.tobytes()})
exr.close()

# read back in via tinyexr (used internally by simpleimageio)
tinyresult = sio.read("gen.exr")
sio.write("test2.exr", tinyresult)
