INC_DIR = -I../../ -I../common

INCLUDES := ../../tinyexr.h
OBJS := tinyexr.o cube2longlat.o

CXXFLAGS := -fsanitize=address -std=c++11 -O2
LDFLAGS := -fsanitize=address

TARGET=cube2longlat

all: $(TARGET)

$(TARGET): $(OBJS) miniz.o
	$(CXX) -o $(TARGET) $(LDFLAGS) $(OBJS) miniz.o

tinyexr.o: ../../tinyexr.cc
	$(CXX) $(CXXFLAGS) -c $(INC_DIR) $<

cube2longlat.o: cube2longlat.cc
	$(CXX) $(CXXFLAGS) -c $(INC_DIR) $<

miniz.o: ../../miniz.c
	$(CC) -c -g -O2 $<

.PHONY: clean
clean:
	rm -rf $(TARGET) $(OBJS)
