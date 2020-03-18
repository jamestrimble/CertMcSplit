CXX := g++
CXXFLAGS := -O3 -g -ggdb -march=native -std=c++17
all: mcsp

mcsp: mcsp.c graph.c graph.h
	$(CXX) $(CXXFLAGS) -Wall -o mcsp graph.c mcsp.c -pthread
