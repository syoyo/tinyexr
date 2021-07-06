INC_DIR = -I../../ -I../common -I ../../deps/miniz

INCLUDES := ../../tinyexr.h
OBJS := miniz.o tinyexr.o cube2longlat.o

CFLAGS := -fsanitize=address -O2
CXXFLAGS := $(CFLAGS) -std=c++11
LDFLAGS := -fsanitize=address

TARGET=cube2longlat
 
all: $(TARGET)

$(TARGET): $(OBJS)
	$(CXX) -o $(TARGET) $(LDFLAGS) $(OBJS)

miniz.o: ../../deps/miniz/miniz.c
	$(CC) $(CFLAGS) -c $(INC_DIR) $<

tinyexr.o: ../../tinyexr.cc
	$(CXX) $(CXXFLAGS) -c $(INC_DIR) $<

cube2longlat.o: cube2longlat.cc
	$(CXX) $(CXXFLAGS) -c $(INC_DIR) $<

.PHONY: clean
clean:
	rm -rf $(TARGET) $(OBJS)
