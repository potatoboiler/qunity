# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.22

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Disable VCS-based implicit rules.
% : %,v

# Disable VCS-based implicit rules.
% : RCS/%

# Disable VCS-based implicit rules.
% : RCS/%,v

# Disable VCS-based implicit rules.
% : SCCS/s.%

# Disable VCS-based implicit rules.
% : s.%

.SUFFIXES: .hpux_make_needs_suffix_list

# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/potatoboiler/ocaml-qunity/staq

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/potatoboiler/ocaml-qunity/build

# Include any dependencies generated for this target.
include src/tools/CMakeFiles/staq_device_generator.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include src/tools/CMakeFiles/staq_device_generator.dir/compiler_depend.make

# Include the progress variables for this target.
include src/tools/CMakeFiles/staq_device_generator.dir/progress.make

# Include the compile flags for this target's objects.
include src/tools/CMakeFiles/staq_device_generator.dir/flags.make

src/tools/CMakeFiles/staq_device_generator.dir/device_generator.cpp.o: src/tools/CMakeFiles/staq_device_generator.dir/flags.make
src/tools/CMakeFiles/staq_device_generator.dir/device_generator.cpp.o: /home/potatoboiler/ocaml-qunity/staq/src/tools/device_generator.cpp
src/tools/CMakeFiles/staq_device_generator.dir/device_generator.cpp.o: src/tools/CMakeFiles/staq_device_generator.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/potatoboiler/ocaml-qunity/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object src/tools/CMakeFiles/staq_device_generator.dir/device_generator.cpp.o"
	cd /home/potatoboiler/ocaml-qunity/build/src/tools && /usr/bin/g++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT src/tools/CMakeFiles/staq_device_generator.dir/device_generator.cpp.o -MF CMakeFiles/staq_device_generator.dir/device_generator.cpp.o.d -o CMakeFiles/staq_device_generator.dir/device_generator.cpp.o -c /home/potatoboiler/ocaml-qunity/staq/src/tools/device_generator.cpp

src/tools/CMakeFiles/staq_device_generator.dir/device_generator.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/staq_device_generator.dir/device_generator.cpp.i"
	cd /home/potatoboiler/ocaml-qunity/build/src/tools && /usr/bin/g++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/potatoboiler/ocaml-qunity/staq/src/tools/device_generator.cpp > CMakeFiles/staq_device_generator.dir/device_generator.cpp.i

src/tools/CMakeFiles/staq_device_generator.dir/device_generator.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/staq_device_generator.dir/device_generator.cpp.s"
	cd /home/potatoboiler/ocaml-qunity/build/src/tools && /usr/bin/g++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/potatoboiler/ocaml-qunity/staq/src/tools/device_generator.cpp -o CMakeFiles/staq_device_generator.dir/device_generator.cpp.s

# Object files for target staq_device_generator
staq_device_generator_OBJECTS = \
"CMakeFiles/staq_device_generator.dir/device_generator.cpp.o"

# External object files for target staq_device_generator
staq_device_generator_EXTERNAL_OBJECTS =

src/tools/staq_device_generator: src/tools/CMakeFiles/staq_device_generator.dir/device_generator.cpp.o
src/tools/staq_device_generator: src/tools/CMakeFiles/staq_device_generator.dir/build.make
src/tools/staq_device_generator: src/tools/CMakeFiles/staq_device_generator.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/potatoboiler/ocaml-qunity/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable staq_device_generator"
	cd /home/potatoboiler/ocaml-qunity/build/src/tools && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/staq_device_generator.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
src/tools/CMakeFiles/staq_device_generator.dir/build: src/tools/staq_device_generator
.PHONY : src/tools/CMakeFiles/staq_device_generator.dir/build

src/tools/CMakeFiles/staq_device_generator.dir/clean:
	cd /home/potatoboiler/ocaml-qunity/build/src/tools && $(CMAKE_COMMAND) -P CMakeFiles/staq_device_generator.dir/cmake_clean.cmake
.PHONY : src/tools/CMakeFiles/staq_device_generator.dir/clean

src/tools/CMakeFiles/staq_device_generator.dir/depend:
	cd /home/potatoboiler/ocaml-qunity/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/potatoboiler/ocaml-qunity/staq /home/potatoboiler/ocaml-qunity/staq/src/tools /home/potatoboiler/ocaml-qunity/build /home/potatoboiler/ocaml-qunity/build/src/tools /home/potatoboiler/ocaml-qunity/build/src/tools/CMakeFiles/staq_device_generator.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : src/tools/CMakeFiles/staq_device_generator.dir/depend

