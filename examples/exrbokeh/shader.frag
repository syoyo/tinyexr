varying vec2 texcoord;

uniform sampler2D tex;

uniform float intensity_scale;
uniform float gamma;

void main()
{
	vec4 rgba = texture2D(tex, texcoord);
	gl_FragColor = vec4(pow(intensity_scale * rgba.rgb, vec3(1.0 / gamma)), 1.0);
}
