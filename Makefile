.PHONY: all build run
all: build run
build:
	go build -o pfuzz

run:
	./pfuzz