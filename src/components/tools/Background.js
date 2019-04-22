import React from "react";
import cx from "classnames";

import "./_background.scss";
import { SettingsContext } from "../../contexts";

const Background = () => (
  <SettingsContext.Consumer>
    {context =>
      context.bgImg || context.bgColor ? (
        <div
          className={cx("Background", {
            "Background--tiled": context.bgStyle === "tile",
            "Background--contain": context.bgStyle === "contain",
            "Background--stretch": context.bgStyle === "stretch"
          })}
        >
          <div
            style={{
              backgroundImage: `url(${context.bgImg})`,
              backgroundColor: `${
                context.bgColor ? context.bgColor : "#5f9ea0"
              }`
            }}
          />
        </div>
      ) : null
    }
  </SettingsContext.Consumer>
);
export default Background;
