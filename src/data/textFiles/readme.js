const generateRows = () => {
  const rows = [
    {
      title: "Introduction",
      image:
        "https://appstickers-cdn.appadvice.com/1164831016/819286823/18ab4614722102b2a0def24dda1ea4bd-1.gif",
      content: `
      Hi, this is a small recreation of a Windows 98 Desktop.
      I developed a component library just to learn some browser stuff and this seemed like the best way to test it out<br/>
      The focus was on trying to capture the feel of my own personal computer circa 2000-2002 (terrible monitor included) rather than a straight copy of Windows 98 so theres's some big differences. Lemme know if you find any bugs!
      `
    },
    {
      title: "Features",
      image: "http://worldartsme.com/images/work-assignment-list-clipart-1.jpg",
      content: `
        <ul>
          <li>W98 UI</li>
          <li>CRT Flicker</li>
          <li>Launch and shut down screens</li>
          <li>Desktop interface</li>
          <li>StartMenu</li>
          <li>Resizable windows</li>
          <li>Notepad</li>
          <li>Custom backgrounds (see Start -> Settings -> Control Panel)</li>
          <li>Save Notepad files for later, Save As new files</li>
          <li>Annoying Floppy Disk Lag</li>
        </ul>
      `
    },
    {
      title: "FAQ",
      image:
        "https://encrypted-tbn0.gstatic.com/images?q=tbn:ANd9GcQRX6w3EFRXeOcn6IvxIHNU8S7NU-HNKLtJd8CBYvAiuWZzbu0xNDvBFubV",
      content: `
        <ul>
          <li>What's that annoying flicker?<br>I added a CRT effect, you can disable it via Start -> Settings -> Control Panel</li>
          <li>Why the weird screen size?<br>
            On desktop I'm trying to match up with my old monitor, basically everyone used a 4:3 resolution back then too, you can change this in the control panel too<br/>
            On mobile, 100vh results in an annoying scroll on some browsers that clashes like crazy with the dragging and droppig.
          </li>
          <li>Paint is broken<br/>I know, it's poc and isn't something I want to work on improving atm</li>
          <li>Can I delete files?<br /> Not yet, unless you delete local storage</li>
          <li>The launch screen was cool, can I play it again?<br/>Yep, you'll have to go through the shut down screen first though</li>
          <li>Why that background as default?<br />I plan on changing this often enough</li>
        </ul>
      `
    },
    {
      title: "Technical stuff",
      image: "http://clipart-library.com/image_gallery/91835.jpg",
      content: `
        This site is built with React 16 (pre-hooks, I have my reasons).<br />
        State management is handled via React's Context API, as I never worked with it before I need to do a huge refactoring of dumb bits hanging around.<br />
        'react-rnd' was used extensively to manage windows.<br />
        Limited tests are done on the context functions and Cypress will be used to ensure core operations work okay.<br/>
        System storage is currently handled via localStorage<br/>
        Whilst minesweeper, skifree and paint are included here, they are quite lazily chucked in iframes that serve only as a proof of concept<br/>
        @TODO Add list of concessions to work on mobile
        @TODO thorough documentation of internal API following refactoring is needed
        `
    },
    {
      title: "Goals",
      image: "http://clipart-library.com/img/1577254.png",
      content: `
        <ul>
          <li>Full desktop as exportable component</li>
          <li>Storing system data on server with accounts instead of local storage</li>
          <li>Better flexibility RE: directories</li>
          <li>Recreation of MSN or AIM as an example of a multiwindow background app</li>
          <li>Recreations of smaller apps (minesweeper, calculator, image viewer)</li>
          <li>Semi operational Internet Explorer (including nav) to work with same origin-sites (could be cool with gatsby)</li>
        </ul>
      `
    }
  ];

  return rows
    .map(
      r => `
    <tr>
      <td bgcolor="black" width="80px" align="right">
        <font color="white" id="introduction">
          ${r.title}<br/>
          <img src="${r.image}" width="60px" />
        </font>
      </td>
      <td bgcolor="lightgrey">
        ${r.content}
      </td>
    </tr>
  `
    )
    .join("");
};

const marqueeGen = () =>
  [
    {
      href: "https://github.com/padraigfl/packard-belle-desktop",
      title: "Source Code"
    },
    {
      href: "https://www.npmjs.com/package/packard-belle",
      title: "Component Library"
    },
    {
      href: "https://www.linkedin.com/in/padraig-f-334b8764/",
      title: "LinkedIn"
    },
    { href: "https://www.buymeacoffee.com/padraig", title: "$$$?" },
    {
      href: "https://github.com/1j01/98#related-projects",
      title: "Similar projects"
    }
  ]
    .map(
      l =>
        `<a href="${l.href}" target="_blank" norel="noopen noreferrer">${
          l.title
        }</a>`
    )
    .join(" | ");

const readmeHTML = `
<style>
font * {font-family: 'Comic Sans MS' !important;}
blink {
  -webkit-animation: 1s linear infinite condemned_blink_effect; // for android
  animation: 1s linear infinite condemned_blink_effect;
}
@-webkit-keyframes condemned_blink_effect { // for android
  0% {
      visibility: hidden;
  }
  50% {
      visibility: hidden;
  }
  100% {
      visibility: visible;
  }
}
@keyframes condemned_blink_effect {
  0% {
      visibility: hidden;
  }
  50% {
      visibility: hidden;
  }
  100% {
      visibility: visible;
  }
}
</style>
<font size="4" >
  <marquee bgcolor="red" color="white">
    ${marqueeGen()}
  </marquee>
  <table bgcolor="grey" width="100%">
    <thead>
      <tr>
        <td colspan="2" valign="center">
          <font size="7"><b>README</b></font>
        </td>
      </tr>
    </thead>
    <tbody valign="top">
      ${generateRows()}
    </tbody>
    <tfoot valign="top">
      <tr><td>(c)1999</td>
      <td>
      <blink>

      <img align="right" width="200px" src="https://unixtitan.net/images/give-clipart-thank-you-gift-7.gif" />
      </blink>
      </td></tr>
    </tfoot>
  </table>
 </font>
`;

export default readmeHTML;
