varying vec2 texcoord;

uniform sampler2D tex;

uniform float intensity_scale;

void main()
{
	vec4 rgba = texture2D(tex, texcoord);
	gl_FragColor = vec4(intensity_scale * rgba.rgb, 1.0);
}
