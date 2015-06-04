project(tinyexr)
cmake_minimum_required(VERSION 2.8)

set(tinyexr-Source
	${CMAKE_CURRENT_SOURCE_DIR}/../tinyexr.cc
	${CMAKE_CURRENT_SOURCE_DIR}/../tinyexr.h
	)

add_library(tinyexr
			${tinyexr-Source}
	)

#Installation
#install ( TARGETS
#  tinyexr
#  DESTINATION
#  lib
#  )
#install ( FILES
#  tinyexr.h
#  DESTINATION
#  include
#  )
