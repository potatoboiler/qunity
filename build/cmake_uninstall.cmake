IF(POLICY CMP0012)
    CMAKE_POLICY(SET CMP0012 NEW)
ENDIF()

if(NOT EXISTS "/home/potatoboiler/ocaml-qunity/build/install_manifest.txt")
  message(FATAL_ERROR "Cannot find install manifest: /home/potatoboiler/ocaml-qunity/build/install_manifest.txt")
endif()

file(READ "/home/potatoboiler/ocaml-qunity/build/install_manifest.txt" files)
string(REGEX REPLACE "\n" ";" files "${files}")
foreach(file ${files})
  message(STATUS "Uninstalling $ENV{DESTDIR}${file}")
  if(IS_SYMLINK "$ENV{DESTDIR}${file}" OR EXISTS "$ENV{DESTDIR}${file}")
    exec_program(
      "/usr/bin/cmake" ARGS "-E remove \"$ENV{DESTDIR}${file}\""
      OUTPUT_VARIABLE rm_out
      RETURN_VALUE rm_retval
      )
    if(NOT "${rm_retval}" STREQUAL 0)
      message(FATAL_ERROR "Problem when removing $ENV{DESTDIR}${file}")
    endif()
  else(IS_SYMLINK "$ENV{DESTDIR}${file}" OR EXISTS "$ENV{DESTDIR}${file}")
    message(STATUS "File $ENV{DESTDIR}${file} does not exist.")
  endif()
endforeach()

if(NOT "")
    message(STATUS "Removing /usr/local/lib/cmake/staq")
    if("OFF")
        message(STATUS "Removing ")
    endif()
else()
    message(STATUS "Removing /usr/local")
endif()
