cmake_minimum_required(VERSION 3.26)
project(agic LANGUAGES C)

find_package(FLEX)
FLEX_TARGET(agic_flex src/agic/agic.lex ${CMAKE_CURRENT_BINARY_DIR}/lex.yy.c
    DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/lex.yy.h)

find_package(BISON)
BISON_TARGET(agic_parser src/agic/agic.y ${CMAKE_CURRENT_BINARY_DIR}/y.tab.c
    DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/y.tab.h)

ADD_FLEX_BISON_DEPENDENCY(agic_flex agic_parser)

include_directories(${CMAKE_CURRENT_BINARY_DIR})
include_directories(src/agic)

add_executable(agic
    src/agic/agiavis.c
    src/agic/agicore.c
    src/agic/agierr.c
    src/agic/agifunc.c
    src/agic/agigoto.c
    src/agic/agiobj.c
    src/agic/agistr.c
    src/agic/agitok.c
    src/agic/boolean.c
    ${FLEX_agic_flex_OUTPUTS}
    ${BISON_agic_parser_OUTPUTS}
)

add_executable(agiglue
    src/agiglue/agiglue.c)