cmake_minimum_required(VERSION 3.16)
project(exception-lower LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# LLVM's own LLVMConfigVersion.cmake enforces *exact* major.minor matching,
# so we cannot express "14 or newer" via find_package's version argument.
# Locate any LLVM and verify the major version ourselves.
find_package(LLVM REQUIRED CONFIG)

if(LLVM_VERSION_MAJOR LESS 14)
  message(FATAL_ERROR
    "exception-lower requires LLVM 14 or newer; found ${LLVM_PACKAGE_VERSION}")
endif()

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

include_directories(${LLVM_INCLUDE_DIRS})
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

add_executable(exception-lower
  main.cpp
  ExceptionLowerPass.cpp
)

# Map component names to library targets.
llvm_map_components_to_libnames(LLVM_LIBS
  Core
  BitReader
  BitWriter
  Passes
  Support
  TransformUtils
  Analysis
)

target_link_libraries(exception-lower PRIVATE ${LLVM_LIBS})
