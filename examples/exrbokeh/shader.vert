#version 110

attribute vec2 in_position;
attribute vec2 in_texcoord;

varying vec2 texcoord;

void main()
{
    gl_Position = vec4(in_position, 0.0, 1.0);
    texcoord = in_texcoord;
}
